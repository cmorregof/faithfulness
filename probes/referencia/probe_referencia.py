"""Implementación de referencia de los probes (Claude Code), independiente de probes/probe.py.

Sigue la REGLA DE DECISIÓN de probes/BITACORA.md (2026-11-04 12:55). Elecciones que la regla
no fija, declaradas aquí y en el informe:
  - Probe: StandardScaler ajustado solo en entrenamiento + LogisticRegression(C=1.0, lbfgs,
    max_iter=5000), sobre una capa del residual stream.
  - CV anidada para la capa: dentro de cada fold externo, StratifiedGroupKFold(5) interno
    (shuffle, misma semilla que el externo) sobre el entrenamiento; AUROC interno = AUROC de los
    puntajes OOF internos agrupados; empate -> la capa más baja.
  - Grupos: el campo «grupo» del manifiesto (hash del enunciado NL normalizado).
  - Bootstrap de grupos estratificado por clase: cada grupo toma la etiqueta de su primera fila;
    se remuestrean con reemplazo, por separado, los grupos positivos y los negativos (mismo número
    de grupos que en los datos); AUROC sobre las filas de los grupos elegidos.
  - Permutaciones: 100 barajes de y (barajado p con np.random.default_rng(p)), con la selección
    de capa incluida; particiones externas = las de la semilla 0 (con etiquetas reales); una sola
    semilla por permutación. Valor p = (1 + #{nulo >= observado}) / 101, contra el AUROC
    observado de la semilla 0.
  - Superficie: CountVectorizer binario (unigramas y bigramas, min_df=2, vocabulario ajustado en
    entrenamiento) del Lean + log(1+caracteres) y log(1+tokens) del Lean; para «completo»,
    también del NL (vectorizador aparte). Mismo LR C=1 y mismas particiones.
  - Apilado: en cada fold externo, LR(C=1) sobre [puntaje solo_lean, puntaje solo_nl]; se entrena
    con los puntajes OOF internos (capa elegida) del entrenamiento y se aplica a los puntajes
    externos del fold de prueba.
  - «Misma capa en ambas condiciones»: solo_lean evaluado en la capa que eligió completo en ese
    fold.

Uso:
  biblioteca/.venv/bin/python -I probes/referencia/probe_referencia.py \
      --carpeta probes/activaciones/qwen3_4b --nombre qwen3_4b
  (--rapido: 1 semilla, 5 permutaciones; solo para probar que corre)
"""

import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse
import datetime as dt
import json
import re
import time
import warnings

import numpy as np
import pyarrow.parquet as pq
from joblib import Parallel, delayed
from scipy import sparse
from sklearn.feature_extraction.text import CountVectorizer
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import StratifiedGroupKFold
from sklearn.preprocessing import StandardScaler

warnings.filterwarnings("ignore", category=UserWarning)

RAIZ = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DATOS = os.path.join(RAIZ, "probes", "datos", "criticleanbench_test.parquet")
DUDOSAS = os.path.join(RAIZ, "probes", "investigacion", "scripts", "clasificacion_200.tsv")
C = 1.0
SEMILLAS = (0, 1, 2, 3, 4)
N_BOOT = 2000
N_PERM = 100
TOKEN_LEAN = r"[A-Za-z_][A-Za-z0-9_'.]*|\d+|[^\sA-Za-z0-9_]"


# ---------------------------------------------------------------- utilidades

def lr():
    return LogisticRegression(C=C, solver="lbfgs", max_iter=5000)


def ajustar_predecir(Xtr, ytr, Xte):
    esc = StandardScaler().fit(Xtr)
    m = lr().fit(esc.transform(Xtr), ytr)
    return m.predict_proba(esc.transform(Xte))[:, 1]


def particiones(y, g, semilla):
    sgk = StratifiedGroupKFold(n_splits=5, shuffle=True, random_state=semilla)
    return list(sgk.split(np.zeros(len(y)), y, g))


def auc(y, s):
    return float(roc_auc_score(y, s))


def bootstrap(y, g, puntajes, n=N_BOOT, semilla=0):
    """IC 95 % por bootstrap de grupos estratificado por clase.

    puntajes: lista de vectores. Devuelve, por cada vector, (puntual, lo, hi) del AUROC y, si hay
    dos, también de la diferencia puntajes[0] - puntajes[1] sobre los mismos remuestreos.
    """
    rng = np.random.default_rng(semilla)
    ug, primera = np.unique(g, return_index=True)
    clase = y[primera]
    filas = {k: np.flatnonzero(g == k) for k in ug}
    pos, neg = ug[clase == 1], ug[clase == 0]
    reps = []
    for _ in range(n):
        elegidos = np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
        idx = np.concatenate([filas[k] for k in elegidos])
        if len(np.unique(y[idx])) < 2:
            continue
        reps.append([auc(y[idx], s[idx]) for s in puntajes])
    reps = np.array(reps)
    out = []
    for j, s in enumerate(puntajes):
        lo, hi = np.percentile(reps[:, j], [2.5, 97.5])
        out.append((auc(y, s), float(lo), float(hi)))
    if len(puntajes) == 2:
        d = reps[:, 0] - reps[:, 1]
        lo, hi = np.percentile(d, [2.5, 97.5])
        out.append((auc(y, puntajes[0]) - auc(y, puntajes[1]), float(lo), float(hi)))
    return out


# ---------------------------------------------------------------- tareas

def tarea_probe(X, y, g, tr, te, semilla, todas_capas=True):
    """Un fold externo: selección de capa por CV interna y predicción en el fold de prueba."""
    L = X.shape[1]
    interno = particiones(y[tr], g[tr], semilla)
    oof_int = np.zeros((L, len(tr)))
    for capa in range(L):
        Xc = X[tr, capa]
        for a, b in interno:
            oof_int[capa, b] = ajustar_predecir(Xc[a], y[tr][a], Xc[b])
    auc_int = np.array([auc(y[tr], oof_int[c]) for c in range(L)])
    mejor = int(np.flatnonzero(auc_int == auc_int.max())[0])
    capas = range(L) if todas_capas else [mejor]
    pred = np.full((L, len(te)), np.nan)
    for capa in capas:
        pred[capa] = ajustar_predecir(X[tr, capa], y[tr], X[te, capa])
    return {"mejor": mejor, "auc_int": auc_int, "oof_int_mejor": oof_int[mejor], "pred": pred}


def tarea_superficie(lean, nl, y, tr, te, con_nl):
    def rasgos(textos, ajustar=None):
        if ajustar is None:
            v = CountVectorizer(binary=True, ngram_range=(1, 2), min_df=2,
                                token_pattern=TOKEN_LEAN, lowercase=False)
            v.fit([textos[i] for i in tr])
        else:
            v = ajustar
        return v

    bloques_tr, bloques_te = [], []
    fuentes = [lean] + ([nl] if con_nl else [])
    for textos in fuentes:
        v = rasgos(textos)
        bloques_tr.append(v.transform([textos[i] for i in tr]))
        bloques_te.append(v.transform([textos[i] for i in te]))
        largo = np.array([[np.log1p(len(t)), np.log1p(len(re.findall(TOKEN_LEAN, t)))] for t in textos])
        esc = StandardScaler().fit(largo[tr])
        bloques_tr.append(sparse.csr_matrix(esc.transform(largo[tr])))
        bloques_te.append(sparse.csr_matrix(esc.transform(largo[te])))
    m = lr().fit(sparse.hstack(bloques_tr).tocsr(), y[tr])
    return m.predict_proba(sparse.hstack(bloques_te).tocsr())[:, 1]


# ---------------------------------------------------------------- análisis

def cargar(carpeta):
    man = [json.loads(l) for l in open(os.path.join(carpeta, "manifiesto.jsonl"), encoding="utf-8")]
    meta = json.load(open(os.path.join(carpeta, "meta.json"), encoding="utf-8"))
    filas = pq.read_table(DATOS).to_pylist()
    return man, meta, filas


def acts(carpeta, variante, posicion, idx):
    a = np.load(os.path.join(carpeta, f"acts_{variante}_{posicion}.npy"), mmap_mode="r")
    return np.ascontiguousarray(a[idx].astype(np.float32))


def correr_condicion(X, y, g, semillas, jobs, todas_capas=True):
    """Devuelve dict semilla -> lista de 5 (tr, te, resultado)."""
    parts = {s: particiones(y, g, s) for s in semillas}
    trabajos = [(s, k, tr, te) for s in semillas for k, (tr, te) in enumerate(parts[s])]
    res = Parallel(n_jobs=jobs)(
        delayed(tarea_probe)(X, y, g, tr, te, s, todas_capas) for s, k, tr, te in trabajos)
    out = {s: [] for s in semillas}
    for (s, k, tr, te), r in zip(trabajos, res):
        out[s].append((tr, te, r))
    return out


def puntajes(res_cond, n, capa_de=None):
    """OOF de la capa elegida (o de la capa elegida por otra condición) por semilla y promedio."""
    por_semilla = {}
    for s, folds in res_cond.items():
        v = np.full(n, np.nan)
        for k, (tr, te, r) in enumerate(folds):
            capa = r["mejor"] if capa_de is None else capa_de[s][k][2]["mejor"]
            v[te] = r["pred"][capa]
        por_semilla[s] = v
    return np.mean(list(por_semilla.values()), 0), por_semilla


def curva_capas(res_cond, y):
    """AUROC por capa: puntajes OOF de cada capa promediados entre semillas."""
    n = len(y)
    L = next(iter(res_cond.values()))[0][2]["pred"].shape[0]
    acum = np.zeros((L, n))
    for folds in res_cond.values():
        for tr, te, r in folds:
            acum[:, te] += r["pred"]
    acum /= len(res_cond)
    return [auc(y, acum[c]) for c in range(L)]


def apilado(res_lean, res_nl, y, n):
    por_semilla = {}
    for s in res_lean:
        v = np.full(n, np.nan)
        for (tr, te, rl), (_, _, rn) in zip(res_lean[s], res_nl[s]):
            Ztr = np.c_[rl["oof_int_mejor"], rn["oof_int_mejor"]]
            Zte = np.c_[rl["pred"][rl["mejor"]], rn["pred"][rn["mejor"]]]
            v[te] = ajustar_predecir(Ztr, y[tr], Zte)
        por_semilla[s] = v
    return np.mean(list(por_semilla.values()), 0), por_semilla


def superficie(lean, nl, y, g, semillas, con_nl, jobs):
    por_semilla = {}
    for s in semillas:
        parts = particiones(y, g, s)
        preds = Parallel(n_jobs=jobs)(
            delayed(tarea_superficie)(lean, nl, y, tr, te, con_nl) for tr, te in parts)
        v = np.full(len(y), np.nan)
        for (tr, te), p in zip(parts, preds):
            v[te] = p
        por_semilla[s] = v
    return np.mean(list(por_semilla.values()), 0), por_semilla


def permutaciones(X_por_cond, y, g, n_perm, jobs):
    """Nulo con selección de capa incluida; particiones externas de la semilla 0 (etiquetas reales)."""
    parts = particiones(y, g, 0)
    trabajos = []
    for p in range(n_perm):
        yp = np.random.default_rng(p).permutation(y)
        for cond, X in X_por_cond.items():
            for k, (tr, te) in enumerate(parts):
                trabajos.append((p, cond, k, tr, te, yp))
    res = Parallel(n_jobs=jobs)(
        delayed(tarea_probe)(X_por_cond[c], yp, g, tr, te, 0, False) for p, c, k, tr, te, yp in trabajos)
    puntaje = {}
    for (p, c, k, tr, te, yp), r in zip(trabajos, res):
        v = puntaje.setdefault((p, c), np.full(len(y), np.nan))
        v[te] = r["pred"][r["mejor"]]
    nulo = {c: [] for c in X_por_cond}
    for p in range(n_perm):
        yp = np.random.default_rng(p).permutation(y)
        for c in X_por_cond:
            nulo[c].append(auc(yp, puntaje[(p, c)]))
    return {c: np.array(v) for c, v in nulo.items()}


def p_perm(nulo, obs):
    return float((1 + np.sum(nulo >= obs)) / (len(nulo) + 1))


# ---------------------------------------------------------------- principal

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--carpeta", required=True)
    ap.add_argument("--nombre", required=True)
    ap.add_argument("--salida", default=os.path.join(RAIZ, "probes", "referencia"))
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--rapido", action="store_true")
    a = ap.parse_args()
    t0 = time.time()
    semillas = (0,) if a.rapido else SEMILLAS
    n_perm = 5 if a.rapido else N_PERM

    man, meta, filas = cargar(a.carpeta)
    idx_all = np.array([m["idx"] for m in man])
    y_all = np.array([m["etiqueta"] for m in man])
    g_all = np.array([m["grupo"] for m in man])
    compila = np.array([m["compila"] for m in man]) == 1
    dudosas_id = {int(l.split("\t")[0]) for l in open(DUDOSAS, encoding="utf-8").read().splitlines()[1:]
                  if l.split("\t")[1] == "X-ni"}
    dudosa = np.array([m["id"] in dudosas_id for m in man])
    lean_all = [filas[i]["autoformalization"].strip() for i in idx_all]
    nl_all = [filas[i]["refined_statement"].strip() for i in idx_all]
    variantes = [v for v in ("completo", "solo_lean", "solo_nl", "nl_desemparejado")
                 if v in meta.get("variantes_completas", meta.get("variantes", []))]
    pos_media = {v: ("media_nl" if v == "solo_nl" else "media_lean") for v in variantes}

    R = {"modelo": meta["modelo"], "revision": meta["revision"], "fecha": dt.datetime.now().astimezone().isoformat(timespec="minutes"),
         "semillas": list(semillas), "n_perm": n_perm, "n_boot": N_BOOT, "C": C,
         "n_capas_mas_embeddings": meta["n_capas_mas_embeddings"], "variantes": variantes,
         "n_dudosas_encontradas": int(dudosa.sum())}

    def subconj(nombre, mascara, conds, posicion):
        sel = np.flatnonzero(mascara)
        y, g = y_all[sel], g_all[sel]
        res, pts, pts_sem = {}, {}, {}
        for v in conds:
            pos = posicion if posicion == "ultimo" else pos_media[v]
            X = acts(a.carpeta, v, pos, idx_all[sel])
            res[v] = correr_condicion(X, y, g, semillas, a.jobs)
            pts[v], pts_sem[v] = puntajes(res[v], len(sel))
            print(f"  {nombre}/{posicion}/{v}: {time.time() - t0:.0f} s", flush=True)
        return sel, y, g, res, pts, pts_sem

    def resumen(y, g, pts, pts_sem, res):
        out = {}
        for v in pts:
            punt, lo, hi = bootstrap(y, g, [pts[v]])[0]
            capas = [r["mejor"] for s in res[v] for (_, _, r) in res[v][s]]
            out[v] = {"auroc": punt, "ic": [lo, hi],
                      "por_semilla": [auc(y, pts_sem[v][s]) for s in sorted(pts_sem[v])],
                      "capas_elegidas": capas, "curva_capas": curva_capas(res[v], y)}
        if "completo" in pts and "solo_lean" in pts:
            d = bootstrap(y, g, [pts["completo"], pts["solo_lean"]])[2]
            out["diferencia_completo_menos_solo_lean"] = {
                "punto": d[0], "ic": [d[1], d[2]], "positivo": bool(d[1] > 0),
                "por_semilla": [auc(y, pts_sem["completo"][s]) - auc(y, pts_sem["solo_lean"][s])
                                for s in sorted(pts_sem["completo"])]}
        return out

    # 1. Principal: 450 que compilan, «ultimo», cuatro variantes
    print("principal", flush=True)
    sel, y, g, res, pts, pts_sem = subconj("450", compila, variantes, "ultimo")
    P = resumen(y, g, pts, pts_sem, res)
    n = len(sel)
    # misma capa
    misma, misma_sem = puntajes(res["solo_lean"], n, capa_de=res["completo"])
    d = bootstrap(y, g, [pts["completo"], misma])
    P["solo_lean_misma_capa_que_completo"] = {"auroc": d[1][0], "ic": [d[1][1], d[1][2]],
                                              "diferencia": {"punto": d[2][0], "ic": [d[2][1], d[2][2]]}}
    # apilado
    if "solo_nl" in res:
        apil, _ = apilado(res["solo_lean"], res["solo_nl"], y, n)
        d = bootstrap(y, g, [pts["completo"], apil])
        P["apilado_solo_lean_mas_solo_nl"] = {"auroc": d[1][0], "ic": [d[1][1], d[1][2]],
                                              "completo_menos_apilado": {"punto": d[2][0], "ic": [d[2][1], d[2][2]]}}
    # superficie
    lean, nl = [lean_all[i] for i in sel], [nl_all[i] for i in sel]
    for nombre, con_nl in (("superficie_lean", False), ("superficie_lean_mas_nl", True)):
        sp, _ = superficie(lean, nl, y, g, semillas, con_nl, a.jobs)
        d = bootstrap(y, g, [pts["completo"], sp])
        P[nombre] = {"auroc": d[1][0], "ic": [d[1][1], d[1][2]],
                     "completo_menos_superficie": {"punto": d[2][0], "ic": [d[2][1], d[2][2]]}}
    print(f"  superficie: {time.time() - t0:.0f} s", flush=True)
    # P(Yes)
    for v in variantes:
        q = np.load(os.path.join(a.carpeta, f"pyes_{v}.npy"))[idx_all[sel]]
        masa = q[:, 4] + q[:, 5]
        pyes = q[:, 4] / np.maximum(masa, 1e-12)
        d = bootstrap(y, g, [pts["completo"], pyes]) if v == "completo" else None
        e = {"auroc": bootstrap(y, g, [pyes])[0][0], "ic": list(bootstrap(y, g, [pyes])[0][1:]),
             "masa_media": float(masa.mean()), "masa_min": float(masa.min()),
             "prop_yes_mayor_05": float((pyes > 0.5).mean())}
        if d:
            e["sonda_completo_menos_pyes"] = {"punto": d[2][0], "ic": [d[2][1], d[2][2]]}
        P[f"pyes_{v}"] = e
    # permutaciones
    print("permutaciones", flush=True)
    Xp = {v: acts(a.carpeta, v, "ultimo", idx_all[sel]) for v in ("completo", "solo_lean")}
    nulo = permutaciones(Xp, y, g, n_perm, a.jobs)
    P["permutaciones"] = {}
    obs0 = {v: auc(y, pts_sem[v][0]) for v in Xp}
    for v in Xp:
        P["permutaciones"][v] = {"observado_semilla0": obs0[v], "nulo_media": float(nulo[v].mean()),
                                 "nulo_p95": float(np.percentile(nulo[v], 95)),
                                 "nulo_max": float(nulo[v].max()), "p": p_perm(nulo[v], obs0[v])}
    dn = nulo["completo"] - nulo["solo_lean"]
    do = obs0["completo"] - obs0["solo_lean"]
    P["permutaciones"]["diferencia"] = {"observado_semilla0": do, "nulo_media": float(dn.mean()),
                                        "nulo_p95": float(np.percentile(dn, 95)), "p": p_perm(dn, do)}
    print(f"  permutaciones: {time.time() - t0:.0f} s", flush=True)
    R["principal"] = P
    R["principal"]["n"] = int(n)
    R["principal"]["n_pos"] = int(y.sum())

    # 2. Secundarios
    sec = {}
    for nombre, mascara, conds, pos in (
            ("500_ultimo", np.ones(len(man), bool), ["completo", "solo_lean"], "ultimo"),
            ("450_media", compila, variantes, "media"),
            ("450_sin_dudosas_ultimo", compila & ~dudosa, ["completo", "solo_lean"], "ultimo")):
        print(nombre, flush=True)
        s_sel, s_y, s_g, s_res, s_pts, s_sem = subconj(nombre, mascara, conds, pos)
        sec[nombre] = resumen(s_y, s_g, s_pts, s_sem, s_res)
        sec[nombre]["n"] = int(len(s_sel))
        sec[nombre]["n_pos"] = int(s_y.sum())
    R["secundarios"] = sec
    R["segundos"] = round(time.time() - t0)

    os.makedirs(a.salida, exist_ok=True)
    sufijo = "_rapido" if a.rapido else ""
    ruta = os.path.join(a.salida, f"resultados_referencia_{a.nombre}{sufijo}.json")
    with open(ruta, "w", encoding="utf-8") as fh:
        json.dump(R, fh, ensure_ascii=False, indent=1)
    figura(R, os.path.join(a.salida, f"auroc_por_capa_{a.nombre}{sufijo}.png"))
    print(f"listo en {R['segundos']} s: {ruta}", flush=True)


def figura(R, ruta):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    P = R["principal"]
    fig, ax = plt.subplots(figsize=(7, 4))
    for v in R["variantes"]:
        c = P[v]["curva_capas"]
        ax.plot(range(len(c)), c, marker=".", label=v)
    ax.axhline(P["superficie_lean"]["auroc"], ls="--", c="gray", lw=1, label="superficie (Lean)")
    ax.axhline(P["pyes_completo"]["auroc"], ls=":", c="k", lw=1, label="P(Yes) completo")
    ax.axhline(0.5, c="lightgray", lw=0.8)
    ax.set_xlabel("capa (0 = embeddings)")
    ax.set_ylabel("AUROC (OOF, media de 5 semillas)")
    ax.set_title(f"{R['modelo']}: 450 que compilan, último token")
    ax.legend(fontsize=7)
    fig.tight_layout()
    fig.savefig(ruta, dpi=150)


if __name__ == "__main__":
    main()
