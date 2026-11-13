"""Análisis del prerregistro v2 (probes/prerregistro_v2.md, firmado por Carlos el 4 nov 2026, 22:29).

Implementa las lecturas co-primarias, las 1000 permutaciones con selección de capa sobre las
particiones de las 5 semillas, el apilado y los secundarios. Reutiliza sin cambios
probes/referencia/probe_referencia.py (particiones, AUROC, bootstrap, superficie, carga).

Solver (prerregistro §9.5): regresión logística L2 (C = 1, intercepto sin penalizar) sobre el
entrenamiento estandarizado (StandardScaler: media y desviación poblacional del entrenamiento),
resuelta hasta el óptimo por Newton truncado (gradiente conjugado precondicionado, matriz por
vector) en la base de la SVD del entrenamiento, EN LOTE sobre todas las columnas de etiquetas
(columna 0 = etiquetas reales; 1..P = permutaciones). Como la pérdida es convexa y estrictamente
convexa con L2, el óptimo es único: el mismo que busca sklearn lbfgs. --validar lo comprueba sobre
Qwen3-4B contra resultados_referencia_qwen3_4b.json (±0,005 de AUROC por condición).

Particiones: externas e internas de las semillas 0–4 calculadas una vez con las etiquetas reales
(§9.4). Puntajes: probabilidades OOF promediadas por fila entre semillas. Lectura (i): «ultimo»,
capa por CV anidada (AUROC de los OOF internos; empate -> la capa más baja). Lectura (ii):
«media_lean» (solo_nl: «media_nl»), capa fija ⌊2L/3⌋.

Uso:
  biblioteca/.venv/bin/python -I probes/referencia/prerregistro_v2_analisis.py --validar
  ... --carpeta probes/activaciones/olmo2_7b --nombre olmo2_7b [--n_perm 1000] [--hilos 2]
  ... --meta olmo2_7b gemma3_4b llama31_8b dsprover2_7b      (Holm + metaanálisis)
  --sintetico: datos falsos pequeños para probar que corre.
"""

import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "2")

import argparse
import datetime as dt
import importlib.util
import json
import sys
import time

import numpy as np
import torch
from scipy.stats import norm, rankdata

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(os.path.dirname(AQUI))
_spec = importlib.util.spec_from_file_location("probe_referencia", os.path.join(AQUI, "probe_referencia.py"))
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

SEMILLAS = (0, 1, 2, 3, 4)
N_PERM = 1000
C = 1.0
TOL_GRAD = 1e-5
DT = torch.float64


# ------------------------------------------------------------------ solver en lote

def estandarizar(Xtr, Xte):
    mu = Xtr.mean(0)
    sd = Xtr.std(0)
    sd[sd == 0] = 1.0
    return (Xtr - mu) / sd, (Xte - mu) / sd


def base_svd(Ztr, Zte):
    U, S, Vt = torch.linalg.svd(Ztr, full_matrices=False)
    k = S > max(float(S[0]) * 1e-9, 1e-12)
    if not bool(k.any()):  # rasgos constantes (p. ej. capa 0 en «ultimo»): solo el intercepto
        return torch.zeros(Ztr.shape[0], 1, dtype=Ztr.dtype), torch.zeros(Zte.shape[0], 1, dtype=Zte.dtype)
    U, S, Vt = U[:, k], S[k], Vt[k]
    return U * S, Zte @ Vt.T   # A (n×r), B (m×r)


def newton_lote(A, Y, max_newton=60, max_cg=60):
    """min_θ C Σ_i softplus(-(2y-1)(A β + b)) + ½‖β‖², para cada columna de Y (n×P) a la vez."""
    n, r = A.shape
    P = Y.shape[1]
    beta = torch.zeros(r, P, dtype=DT)
    b = torch.zeros(1, P, dtype=DT)
    signo = 2 * Y - 1
    A2 = A * A

    def objetivo(beta, b):
        s = A @ beta + b
        return C * torch.nn.functional.softplus(-signo * s).sum(0) + 0.5 * (beta * beta).sum(0)

    f = objetivo(beta, b)
    for _ in range(max_newton):
        s = A @ beta + b
        p = torch.sigmoid(s)
        w = p * (1 - p)
        gb = C * A.T @ (p - Y) + beta
        gi = C * (p - Y).sum(0, keepdim=True)
        gmax = torch.maximum(gb.abs().amax(0), gi.abs().amax(0))
        activos = gmax > TOL_GRAD
        if not activos.any():
            break
        # PCG con precondicionador de Jacobi sobre H = C Ãᵀ W Ã + Λ
        Mb = C * A2.T @ w + 1.0
        Mi = C * w.sum(0, keepdim=True) + 1e-12
        def Hv(vb, vi):
            t = w * (A @ vb + vi)
            return C * A.T @ t + vb, C * t.sum(0, keepdim=True)
        xb, xi = torch.zeros_like(gb), torch.zeros_like(gi)
        rb, ri = -gb, -gi
        zb, zi = rb / Mb, ri / Mi
        pb, pi = zb.clone(), zi.clone()
        rz = (rb * zb).sum(0) + (ri * zi).sum(0)
        nr0 = torch.sqrt((rb * rb).sum(0) + (ri * ri).sum(0))
        for _ in range(max_cg):
            qb, qi = Hv(pb, pi)
            alfa = rz / ((pb * qb).sum(0) + (pi * qi).sum(0)).clamp_min(1e-300)
            xb += alfa * pb; xi += alfa * pi
            rb -= alfa * qb; ri -= alfa * qi
            nr = torch.sqrt((rb * rb).sum(0) + (ri * ri).sum(0))
            if bool((nr <= 1e-3 * nr0.clamp_max(1.0) * nr0 + 1e-14).all()):
                break
            zb, zi = rb / Mb, ri / Mi
            rz2 = (rb * zb).sum(0) + (ri * zi).sum(0)
            pb = zb + (rz2 / rz.clamp_min(1e-300)) * pb
            pi = zi + (rz2 / rz.clamp_min(1e-300)) * pi
            rz = rz2
        xb = xb * activos; xi = xi * activos
        # búsqueda lineal por columna (paso 1, se parte a la mitad si el objetivo sube)
        paso = torch.ones(P, dtype=DT)
        for _ in range(30):
            fn = objetivo(beta + paso * xb, b + paso * xi)
            malos = (fn > f + 1e-12) & activos
            if not malos.any():
                break
            paso = torch.where(malos, paso / 2, paso)
        beta = beta + paso * xb
        b = b + paso * xi
        f = objetivo(beta, b)
    return beta, b


def ajustar_predecir_lote(Xtr, Ytr, Xte):
    """Xtr (n×d), Ytr (n×P) 0/1 -> probabilidades en Xte (m×P)."""
    Ztr, Zte = estandarizar(Xtr, Xte)
    A, B = base_svd(Ztr, Zte)
    beta, b = newton_lote(A, Ytr)
    return torch.sigmoid(B @ beta + b)


def auc_cols(Y, S):
    """AUROC por columna (Y, S: n×P numpy), con empates promediados."""
    R = rankdata(S, axis=0)
    n1 = Y.sum(0)
    n0 = Y.shape[0] - n1
    return (R * Y).sum(0) - n1 * (n1 + 1) / 2, n1 * n0


def auc_col(Y, S):
    num, den = auc_cols(Y, S)
    return num / den


# ------------------------------------------------------------------ pipeline

def particiones_fijas(y, g, semillas):
    out = {}
    for s in semillas:
        ext = ref.particiones(y, g, s)
        out[s] = [(tr, te, ref.particiones(y[tr], g[tr], s)) for tr, te in ext]
    return out


def condicion(X, Y, parts, capa_fija=None, guardar_interno=False, log=None):
    """X: (n, L, d) float32 numpy; Y: (n, P) 0/1. Devuelve probabilidades OOF promediadas entre
    semillas (n×P), capas elegidas (por semilla y fold, columna 0) y, si se pide, los OOF internos
    de la capa elegida (columna 0) para el apilado."""
    n, L, _ = X.shape
    P = Y.shape[1]
    Yt = torch.from_numpy(Y.astype(np.float64))
    capas = range(L) if capa_fija is None else [capa_fija]
    acum = np.zeros((n, P))
    elegidas, internos = {}, {}
    for s, folds in parts.items():
        for k, (tr, te, interno) in enumerate(folds):
            ytr = Y[tr]
            oof_int = {}
            pred = {}
            for c in capas:
                Xc = torch.from_numpy(X[:, c].astype(np.float64))
                Xtr = Xc[tr]
                if capa_fija is None or guardar_interno:
                    # con capa fija, los OOF internos solo hacen falta para la columna 0 (apilado)
                    Pi = P if capa_fija is None else 1
                    o = np.zeros((len(tr), Pi))
                    for a, bb in interno:
                        o[bb] = ajustar_predecir_lote(Xtr[a], Yt[tr][a][:, :Pi], Xtr[bb]).numpy()
                    oof_int[c] = o
                pred[c] = ajustar_predecir_lote(Xtr, Yt[tr], Xc[te]).numpy()
            if capa_fija is None:
                aucs = np.stack([auc_col(ytr, oof_int[c]) for c in capas])  # (L, P)
                mejor = aucs.argmax(0)  # primera aparición del máximo = capa más baja
            else:
                mejor = np.full(P, capa_fija)
            P_te = np.stack([pred[c] for c in capas])  # (L', m, P)
            idx = mejor if capa_fija is None else np.zeros(P, int)
            acum[te] += P_te[idx, :, np.arange(P)].T
            elegidas[(s, k)] = int(mejor[0])
            if guardar_interno:
                internos[(s, k)] = (oof_int[int(mejor[0])][:, 0], pred[int(mejor[0])][:, 0])
            if log:
                log(f"semilla {s} fold {k}")
    return acum / len(parts), elegidas, internos


def apilado_obs(int_lean, int_nl, y, parts):
    """Apilado como en la referencia: LR(C=1) sobre [puntaje solo_lean, puntaje solo_nl] (columna 0)."""
    n = len(y)
    acum = np.zeros(n)
    for s, folds in parts.items():
        for k, (tr, te, _) in enumerate(folds):
            Ztr = np.c_[int_lean[(s, k)][0], int_nl[(s, k)][0]]
            Zte = np.c_[int_lean[(s, k)][1], int_nl[(s, k)][1]]
            acum[te] += ref.ajustar_predecir(Ztr, y[tr], Zte)
    return acum / len(parts)


def capa_fija_de(L1):
    return (2 * (L1 - 1)) // 3


# ------------------------------------------------------------------ principal

def analizar(carpeta, nombre, n_perm, salida, hilos, sintetico=False, n_perm_i=None):
    """n_perm: permutaciones de la lectura (ii); n_perm_i: de la lectura (i) (por defecto, las mismas)."""
    n_perm_i = n_perm if n_perm_i is None else n_perm_i
    torch.set_num_threads(hilos)
    t0 = time.time()
    log = lambda m: print(f"[{time.time() - t0:.0f} s] {m}", flush=True)
    if sintetico:
        rng = np.random.default_rng(0)
        n, L1, d = 120, 5, 24
        g = np.array([f"g{i // 2}" for i in range(n)])
        y = (rng.random(n) < 0.5).astype(int)
        Xs = {v: rng.normal(size=(n, L1, d)).astype(np.float32) for v in ("completo", "solo_lean", "solo_nl")}
        Xs["completo"][:, :, 0] += y[:, None]
        Xs["solo_lean"][:, :, 0] += 0.5 * y[:, None]
        Xm = {v: x * 0.5 for v, x in Xs.items()}
        dudosa = np.zeros(n, bool)
        meta = {"modelo": "sintetico", "revision": "-"}
        pyes = None
        X_ult, X_med = (lambda v, sel: Xs[v][sel]), (lambda v, sel: Xm[v][sel])
        mascara = np.ones(n, bool)
        lean_all = nl_all = None
    else:
        man, meta, filas = ref.cargar(carpeta)
        L1 = meta["n_capas_mas_embeddings"]
        idx_all = np.array([m["idx"] for m in man])
        y_all = np.array([m["etiqueta"] for m in man])
        g_all = np.array([m["grupo"] for m in man])
        mascara = np.array([m["compila"] for m in man]) == 1
        dud_id = {int(l.split("\t")[0]) for l in open(ref.DUDOSAS, encoding="utf-8").read().splitlines()[1:]
                  if l.split("\t")[1] == "X-ni"}
        dudosa_all = np.array([m["id"] in dud_id for m in man])
        sel = np.flatnonzero(mascara)
        y, g, dudosa = y_all[sel], g_all[sel], dudosa_all[sel]
        X_ult = lambda v, s: ref.acts(carpeta, v, "ultimo", idx_all[s])
        X_med = lambda v, s: ref.acts(carpeta, v, "media_nl" if v == "solo_nl" else "media_lean", idx_all[s])
        lean_all = [filas[i]["autoformalization"].strip() for i in idx_all]
        nl_all = [filas[i]["refined_statement"].strip() for i in idx_all]
        pyes = {v: np.load(os.path.join(carpeta, f"pyes_{v}.npy"))[idx_all[sel]] for v in ("completo", "solo_lean")}
        sel_local = sel
    n = len(y)
    if sintetico:
        sel_local = np.arange(n)
    ell = capa_fija_de(L1)
    parts = particiones_fijas(y, g, SEMILLAS)
    n_tot = max(n_perm, n_perm_i)  # corrección del 5 nov, 08:4x: antes solo n_perm (lectura ii)
    Y = np.empty((n, 1 + n_tot), dtype=np.int8)
    Y[:, 0] = y
    for p in range(n_tot):
        Y[:, 1 + p] = np.random.default_rng(p).permutation(y)
    R = {"modelo": meta["modelo"], "revision": meta["revision"], "nombre": nombre,
         "fecha": dt.datetime.now().astimezone().isoformat(timespec="minutes"),
         "prerregistro": "probes/prerregistro_v2.md", "n": int(n), "n_pos": int(y.sum()),
         "n_capas_mas_embeddings": int(L1), "capa_fija_lectura_ii": int(ell), "n_perm": n_perm,
         "semillas": list(SEMILLAS), "n_boot": ref.N_BOOT}
    lecturas = {}
    for lect, Xf, cf in (("i_ultimo_cv", X_ult, None), ("ii_media_lean_capa_fija", X_med, ell)):
        res, ints, capas = {}, {}, {}
        Yl = Y[:, :1 + (n_perm_i if cf is None else n_perm)]
        for v in ("completo", "solo_lean"):
            prob, el, it = condicion(Xf(v, sel_local), Yl, parts, capa_fija=cf, guardar_interno=True,
                                     log=None)
            res[v], ints[v], capas[v] = prob, it, el
            log(f"{lect} {v}")
        prob_nl, _, it_nl = condicion(Xf("solo_nl", sel_local), Y[:, :1], parts, capa_fija=cf, guardar_interno=True)
        auc_c, auc_l = auc_col(Yl, res["completo"]), auc_col(Yl, res["solo_lean"])
        delta = auc_c - auc_l
        obs, nulo = float(delta[0]), delta[1:]
        np_l = len(nulo)
        p = float((1 + np.sum(nulo >= obs)) / (np_l + 1)) if np_l else None
        pc, pl = res["completo"][:, 0], res["solo_lean"][:, 0]
        b = ref.bootstrap(y, g, [pc, pl])
        # DE bootstrap de Δ para el metaanálisis (mismos remuestreos que ref.bootstrap)
        de = bootstrap_de(y, g, pc, pl)
        apil = apilado_obs(ints["solo_lean"], it_nl, y, parts)
        ba = ref.bootstrap(y, g, [pc, apil])
        e = {"auroc_completo": b[0][0], "ic_completo": list(b[0][1:]),
             "auroc_solo_lean": b[1][0], "ic_solo_lean": list(b[1][1:]),
             "delta": b[2][0], "ic_delta": list(b[2][1:]), "de_bootstrap_delta": de,
             "auroc_solo_nl": ref.auc(y, prob_nl[:, 0]),
             "apilado": ba[1][0], "completo_menos_apilado": ba[2][0], "ic_completo_menos_apilado": list(ba[2][1:]),
             "apilado_ic_sobre_0": bool(ba[2][1] > 0),
             "perm": {"n": np_l, "observado": obs, "p": p,
                      "nulo_media": float(nulo.mean()) if np_l else None,
                      "nulo_p95": float(np.percentile(nulo, 95)) if np_l else None,
                      "nulo_max": float(nulo.max()) if np_l else None},
             "capas_elegidas": {v: list(capas[v].values()) for v in capas}}
        # sensibilidad: sin las 44 dudosas (observado + bootstrap, sin permutaciones)
        if dudosa.any():
            m = ~dudosa
            bs = ref.bootstrap(y[m], g[m], [pc[m], pl[m]])
            e["sensibilidad_sin_dudosas"] = {"n": int(m.sum()), "delta_sobre_puntajes_del_primario": bs[2][0],
                                             "ic": list(bs[2][1:]),
                                             "nota": "puntajes OOF del primario restringidos a las filas no dudosas"}
        lecturas[lect] = e
        np.savez_compressed(os.path.join(salida, f"v2_puntajes_{nombre}_{lect}.npz"),
                            y=y, completo=pc, solo_lean=pl, solo_nl=prob_nl[:, 0], apilado=apil,
                            nulo_delta=nulo)
    R["lecturas"] = lecturas
    if pyes is not None:
        q = pyes["completo"]
        masa = q[:, 4] + q[:, 5]
        R["secundario_pyes_completo"] = {"auroc": ref.auc(y, q[:, 4] / np.maximum(masa, 1e-12)),
                                         "masa_media": float(masa.mean()),
                                         "interpretable": bool(masa.mean() >= 0.5)}
    if lean_all is not None:
        lean = [lean_all[i] for i in sel_local]
        nl = [nl_all[i] for i in sel_local]
        sp, _ = ref.superficie(lean, nl, y, g, SEMILLAS, False, hilos)
        R["secundario_superficie_lean"] = {"auroc": ref.auc(y, sp)}
    R["segundos"] = round(time.time() - t0)
    ruta = os.path.join(salida, f"v2_resultados_{nombre}.json")
    json.dump(R, open(ruta, "w", encoding="utf-8"), ensure_ascii=False, indent=1, default=float)
    log(f"listo: {ruta}")
    return R


def bootstrap_de(y, g, a, b, n=ref.N_BOOT, semilla=0):
    rng = np.random.default_rng(semilla)
    ug, primera = np.unique(g, return_index=True)
    clase = y[primera]
    filas = {k: np.flatnonzero(g == k) for k in ug}
    pos, neg = ug[clase == 1], ug[clase == 0]
    d = []
    for _ in range(n):
        el = np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
        idx = np.concatenate([filas[k] for k in el])
        if len(np.unique(y[idx])) < 2:
            continue
        d.append(ref.auc(y[idx], a[idx]) - ref.auc(y[idx], b[idx]))
    return float(np.std(d, ddof=1))


def validar(hilos):
    """Qwen3-4B (ya visto): puntajes OOF del solver en lote frente a la referencia sklearn."""
    torch.set_num_threads(hilos)
    carpeta = os.path.join(RAIZ, "probes", "activaciones", "qwen3_4b")
    man, meta, filas = ref.cargar(carpeta)
    idx = np.array([m["idx"] for m in man if m["compila"] == 1])
    y = np.array([m["etiqueta"] for m in man if m["compila"] == 1])
    g = np.array([m["grupo"] for m in man if m["compila"] == 1])
    R0 = json.load(open(os.path.join(AQUI, "resultados_referencia_qwen3_4b.json"), encoding="utf-8"))["principal"]
    parts = particiones_fijas(y, g, SEMILLAS)
    out = {}
    t0 = time.time()
    for v in ("completo", "solo_lean"):
        X = ref.acts(carpeta, v, "ultimo", idx)
        prob, el, _ = condicion(X, y[:, None], parts)
        a_v2 = ref.auc(y, prob[:, 0])
        a_ref = R0[v]["auroc"]
        capas_ref = R0[v]["capas_elegidas"]
        out[v] = {"auroc_v2": a_v2, "auroc_ref": a_ref, "dif": a_v2 - a_ref, "ok": abs(a_v2 - a_ref) <= 0.005,
                  "capas_iguales": sum(int(a == b) for a, b in zip(el.values(), capas_ref)), "de": len(capas_ref)}
        print(v, out[v], f"{time.time() - t0:.0f} s", flush=True)
    out["segundos"] = round(time.time() - t0)
    json.dump(out, open(os.path.join(AQUI, "v2_validacion_solver_qwen3_4b.json"), "w"), indent=1, default=float)
    return out


def meta(nombres, salida):
    """Holm sobre los 4 modelos nuevos × 2 lecturas y DerSimonian–Laird por lectura (§9.6–9.8)."""
    Rs = {n: json.load(open(os.path.join(salida, f"v2_resultados_{n}.json"), encoding="utf-8")) for n in nombres}
    pruebas = [(n, l, Rs[n]["lecturas"][l]["perm"]["p"]) for n in nombres for l in Rs[n]["lecturas"]]
    orden = sorted(range(len(pruebas)), key=lambda i: pruebas[i][2])
    m = len(pruebas)
    ajust, previo = [None] * m, 0.0
    for j, i in enumerate(orden):
        previo = max(previo, min(1.0, (m - j) * pruebas[i][2]))
        ajust[i] = previo
    tabla = []
    for (n, l, p), pa in zip(pruebas, ajust):
        e = Rs[n]["lecturas"][l]
        tabla.append({"modelo": n, "lectura": l, "delta": e["delta"], "p": p, "p_holm": pa,
                      "apilado_ic_sobre_0": e["apilado_ic_sobre_0"],
                      "pasa": bool(pa < 0.05 and e["apilado_ic_sobre_0"])})
    metas = {}
    for l in ("i_ultimo_cv", "ii_media_lean_capa_fija"):
        d = np.array([Rs[n]["lecturas"][l]["delta"] for n in nombres])
        v = np.array([Rs[n]["lecturas"][l]["de_bootstrap_delta"] for n in nombres]) ** 2
        w = 1 / v
        dfe = (w * d).sum() / w.sum()
        Q = (w * (d - dfe) ** 2).sum()
        tau2 = max(0.0, (Q - (len(d) - 1)) / (w.sum() - (w ** 2).sum() / w.sum()))
        ws = 1 / (v + tau2)
        est = (ws * d).sum() / ws.sum()
        se = np.sqrt(1 / ws.sum())
        metas[l] = {"estimacion": float(est), "ic": [float(est - norm.ppf(.975) * se), float(est + norm.ppf(.975) * se)],
                    "tau2": float(tau2), "Q": float(Q), "modelos_que_pasan_en_esta_lectura":
                    sum(t["pasa"] for t in tabla if t["lectura"] == l)}
    pasan = {n: any(t["pasa"] for t in tabla if t["modelo"] == n) for n in nombres}
    glob = any(metas[l]["ic"][0] > 0 and metas[l]["modelos_que_pasan_en_esta_lectura"] >= 3 for l in metas)
    out = {"modelos": nombres, "pruebas": tabla, "modelos_que_pasan": pasan, "metaanalisis": metas,
           "afirmacion_global": bool(sum(pasan.values()) >= 3 and glob)}
    json.dump(out, open(os.path.join(salida, "v2_meta.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(json.dumps(out, ensure_ascii=False, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--carpeta")
    ap.add_argument("--nombre")
    ap.add_argument("--n_perm", type=int, default=N_PERM, help="permutaciones de la lectura (ii) (y de la (i) si no se da --n_perm_i)")
    ap.add_argument("--n_perm_i", type=int, default=None, help="permutaciones de la lectura (i)")
    ap.add_argument("--hilos", type=int, default=2)
    ap.add_argument("--salida", default=AQUI)
    ap.add_argument("--validar", action="store_true")
    ap.add_argument("--meta", nargs="+")
    ap.add_argument("--sintetico", action="store_true")
    a = ap.parse_args()
    if a.validar:
        validar(a.hilos)
    elif a.meta:
        meta(a.meta, a.salida)
    elif a.sintetico:
        sal = os.path.join(AQUI, "v2_prueba_sintetica")
        os.makedirs(sal, exist_ok=True)
        analizar(None, "sintetico", a.n_perm, sal, a.hilos, sintetico=True, n_perm_i=a.n_perm_i)
    else:
        analizar(a.carpeta, a.nombre, a.n_perm, a.salida, a.hilos, n_perm_i=a.n_perm_i)


if __name__ == "__main__":
    main()
