"""Análisis del Nivel B (pares mínimos certificados): prueba PAREADA dentro de cada problema.

Sigue el BORRADOR probes/nivel_b/regla_borrador.md (no aprobado). No corre sin la marca
APROBADO_regla_decision (lo comprueba lanzar.sh; aquí se comprueba otra vez salvo --prueba).
Reutiliza, sin modificarlo, probes/referencia/probe_referencia.py (probe, CV anidada de capa,
particiones, superficie). Lo nuevo:

  - Filas de entrenamiento: las variantes infieles (y = 0) y fieles (y = 1) de los pares; los
    originales no entrenan (se puntúan aparte, como control).
  - Particiones: StratifiedGroupKFold(5) agrupado por ARCHIVO fuente (columna `archivo` del índice;
    revisor Fable, 2026-11-04; antes, por enunciado), semillas 0–4, idénticas en todas las
    condiciones; capa por CV anidada (como la referencia). La unidad del estadístico pareado y del
    bootstrap principal sigue siendo el origen; el bootstrap por archivo se reporta como sensibilidad.
  - Decisión: positivo exige además que completo − superficie cruzada NL–Lean (control 6) no quede
    entero por debajo de 0 (condición añadida por el revisor; estaba propuesta en regla_borrador.md).
  - Estadístico: AUROC pareada = media, sobre orígenes, de la fracción de sus pares en que la fiel
    puntúa más alto que la infiel (empate = 0,5), con los puntajes OOF promediados entre semillas.
  - Prueba central: AUROC_p(completo) − AUROC_p(solo_lean); IC 95 % por bootstrap de orígenes
    (2000, semilla 0). Positivo si el IC queda entero por encima de 0 y hay ≥ --umbral_pares pares.
  - Nulo por permutación: 100 permutaciones que intercambian al azar los roles dentro de cada par
    (np.random.default_rng(p)), con particiones de la semilla 0 y selección de capa incluida.
  - Controles: solo_nl (cordura: el NL es idéntico dentro del par → 0,5), nl_desemparejado,
    superficie (n-gramas del Lean y del NL, como la referencia), superficie cruzada NL–Lean
    (numerales del Lean ausentes del NL, relaciones del Lean frente a palabras de relación del NL,
    solapamiento de identificadores), P(Yes), fidelidad ≠ verdad (pares con infiel B, verdadera
    si el original lo es, frente a infieles refutadas), tamaño de edición (por intervalo y
    pendiente de Δpuntaje sobre Δtokens), y original frente a fiel (¿«editado» es la señal?).

Uso:
  biblioteca/.venv/bin/python -I probes/nivel_b/analizar_pares.py \
      --carpeta probes/activaciones/nivel_b_qwen3_4b --indice probes/nivel_b/datos/pares_indice.jsonl \
      --nombre qwen3_4b
  (--rapido: 1 semilla, 5 permutaciones; --prueba: no exige la marca; solo para probar que corre)
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse
import collections
import json
import re
import sys
import time

import numpy as np
from joblib import Parallel, delayed
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(os.path.dirname(AQUI))
sys.path.insert(0, os.path.join(RAIZ, "probes", "referencia"))
import probe_referencia as R  # noqa: E402

N_BOOT, N_PERM = 2000, 100
RENOMBRES = {"D3", "D6"}


# ---------------------------------------------------------------- utilidades pareadas

def w_pares(s, pares):
    """Por par: 1 si la fiel puntúa más que la infiel, 0,5 si empatan, 0 si no."""
    i, f = pares[:, 0], pares[:, 1]
    return np.where(s[f] > s[i], 1.0, np.where(s[f] == s[i], 0.5, 0.0))


def por_origen(w, grupos_par):
    ug, inv = np.unique(grupos_par, return_inverse=True)
    suma = np.bincount(inv, weights=w)
    return suma / np.bincount(inv)


def auc_p(s, pares, gp):
    return float(por_origen(w_pares(s, pares), gp).mean()) if len(pares) else float("nan")


def boot_p(puntajes, pares, gp, n=N_BOOT, semilla=0):
    """IC 95 % por bootstrap de orígenes. Devuelve [(puntual, lo, hi)] por puntaje y, si son dos,
    la diferencia puntajes[0] − puntajes[1]."""
    if len(pares) == 0:
        return [(float("nan"),) * 3] * (len(puntajes) + (len(puntajes) == 2))
    W = np.array([por_origen(w_pares(s, pares), gp) for s in puntajes])  # (k, n_origenes)
    rng = np.random.default_rng(semilla)
    m = W.shape[1]
    reps = np.array([W[:, rng.integers(0, m, m)].mean(1) for _ in range(n)])
    out = [(float(W[j].mean()), *map(float, np.percentile(reps[:, j], [2.5, 97.5]))) for j in range(len(puntajes))]
    if len(puntajes) == 2:
        d = reps[:, 0] - reps[:, 1]
        out.append((float(W[0].mean() - W[1].mean()), *map(float, np.percentile(d, [2.5, 97.5]))))
    return out


def fmt(t):
    return f"{t[0]:.3f} [{t[1]:.3f}; {t[2]:.3f}]"


# ---------------------------------------------------------------- superficie cruzada NL–Lean

PAL = {"le": r"at most|\\le(q)?\b|≤|not exceed|no more than|\\leqslant",
       "lt": r"less than|smaller than|\\lt\b|<|below",
       "ge": r"at least|\\ge(q)?\b|≥|no less than|\\geqslant",
       "gt": r"greater than|larger than|more than|\\gt\b|>|exceeds?",
       "pos": r"positive", "nonneg": r"non-?negative", "ne": r"\\neq?\b|≠|nonzero|non-zero|distinct"}


def rasgos_cruzados(nl, lean):
    num_nl = set(re.findall(r"\d+", nl))
    num_lean = re.findall(r"(?<![\w.])\d+(?![\w.])", lean.split(":=")[0])
    sin = sum(n not in num_nl for n in num_lean)
    f = [sin, len(num_lean) - sin, sum(n not in set(num_lean) for n in num_nl)]
    rel_lean = {k: lean.count(s) for k, s in (("le", "≤"), ("lt", "<"), ("ge", "≥"), ("gt", ">"), ("ne", "≠"))}
    pal = {k: int(bool(re.search(p, nl, re.I))) for k, p in PAL.items()}
    for a in ("le", "lt", "ge", "gt", "ne"):
        for b in PAL:
            f.append(min(rel_lean.get(a, 0), 3) * pal[b])
    ids_nl = set(re.findall(r"\b[A-Za-z]\b", nl))
    ids_le = set(re.findall(r"(?<![\w.])[A-Za-z](?![\w'₀-₉])", lean))
    f += [len(ids_le - ids_nl), len(ids_nl & ids_le) / max(1, len(ids_nl | ids_le)),
          len(re.findall(r"[₀-₉']", lean)), lean.count("¬")]
    return f


def tarea_cruzada(F, y, tr, te):
    esc = StandardScaler().fit(F[tr])
    m = LogisticRegression(C=R.C, max_iter=5000).fit(esc.transform(F[tr]), y[tr])
    return m.predict_proba(esc.transform(F[te]))[:, 1]


def cruzada(F, y, g, semillas):
    v_all = []
    for s in semillas:
        v = np.full(len(y), np.nan)
        for tr, te in R.particiones(y, g, s):
            v[te] = tarea_cruzada(F, y, tr, te)
        v_all.append(v)
    return np.mean(v_all, 0)


# ---------------------------------------------------------------- permutaciones dentro del par

def permutaciones(X_por_cond, y, g, pares, gp, n_perm, jobs):
    parts = R.particiones(y, g, 0)
    trabajos, yps = [], {}
    for p in range(n_perm):
        flip = np.random.default_rng(p).random(len(pares)) < 0.5
        yp = y.copy()
        yp[pares[flip, 0]], yp[pares[flip, 1]] = 1, 0
        yps[p] = (yp, np.where(flip[:, None], pares[:, ::-1], pares))
        for c in X_por_cond:
            for tr, te in parts:
                trabajos.append((p, c, tr, te))
    res = Parallel(n_jobs=jobs)(delayed(R.tarea_probe)(X_por_cond[c], yps[p][0], g, tr, te, 0, False)
                                for p, c, tr, te in trabajos)
    pts = {}
    for (p, c, tr, te), r in zip(trabajos, res):
        v = pts.setdefault((p, c), np.full(len(y), np.nan))
        v[te] = r["pred"][r["mejor"]]
    nulo = {c: np.array([auc_p(pts[(p, c)], yps[p][1], gp) for p in range(n_perm)]) for c in X_por_cond}
    conds = list(X_por_cond)
    if len(conds) >= 2:
        nulo["diferencia"] = nulo[conds[0]] - nulo[conds[1]]
    return nulo


def puntuar_originales(res_cond, X_tr, y, g, X_or, g_or):
    """Puntaje de cada original con el probe del fold cuyo conjunto de prueba contiene su origen."""
    acum, cuenta = np.zeros(len(g_or)), np.zeros(len(g_or))
    for s, folds in res_cond.items():
        for tr, te, r in folds:
            sel = np.isin(g_or, np.unique(g[te]))
            if sel.any():
                c = r["mejor"]
                acum[sel] += R.ajustar_predecir(X_tr[tr, c], y[tr], X_or[sel, c])
                cuenta[sel] += 1
    return acum / np.maximum(cuenta, 1)


# ---------------------------------------------------------------- principal

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--carpeta", required=True)
    ap.add_argument("--indice", default=os.path.join(AQUI, "datos", "pares_indice.jsonl"))
    ap.add_argument("--nombre", required=True)
    ap.add_argument("--salida", default=os.path.join(AQUI, "resultados"))
    ap.add_argument("--jobs", type=int, default=5)
    ap.add_argument("--umbral_pares", type=int, default=400)
    ap.add_argument("--umbral_minimo", type=int, default=200)
    ap.add_argument("--umbral_origenes", type=int, default=300)
    ap.add_argument("--rapido", action="store_true")
    ap.add_argument("--prueba", action="store_true", help="no exige la marca de aprobación (pruebas)")
    a = ap.parse_args()
    if not a.prueba and not os.path.exists(os.path.join(AQUI, "APROBADO_regla_decision")):
        sys.exit("Falta probes/nivel_b/APROBADO_regla_decision (la crea Carlos). No corro.")
    semillas = (0,) if a.rapido else R.SEMILLAS
    n_perm = 5 if a.rapido else N_PERM
    t0 = time.time()

    man = [json.loads(l) for l in open(os.path.join(a.carpeta, "manifiesto.jsonl"), encoding="utf-8")]
    ind = {r["id"]: r for r in map(json.loads, open(a.indice, encoding="utf-8"))}
    # 5 nov 2026: con --indice filtrado (p. ej. datos/pares_indice_principal.jsonl, exclusiones de
    # datos/exclusiones_nivel_b.json) las filas extraídas que no están en el índice se ignoran; `fila`
    # sigue siendo la posición en las activaciones.
    filas = [dict(ind[m["id"]], fila=j, grupo_man=m["grupo"]) for j, m in enumerate(man) if m["id"] in ind]
    tren = [r for r in filas if r["rol"] in ("infiel", "fiel")]
    orig = [r for r in filas if r["rol"] == "original"]
    sel = np.array([r["fila"] for r in tren])
    y = np.array([int(r["rol"] == "fiel") for r in tren])
    # Revisor (Fable, 2026-11-04): los pliegues, la CV interna y las permutaciones se agrupan por
    # ARCHIVO fuente (`archivo` del índice; si falta, el hash del NL): 220 de 472 orígenes de v1
    # compartían archivo con otro (p. ej. a_2, a_3, a_5 de una misma sucesión OEIS). La unidad de
    # remuestreo del estadístico pareado sigue siendo el origen (gp); el bootstrap por archivo se
    # reporta como sensibilidad (ga).
    g_origen = np.array([r["grupo_man"] for r in tren])
    g = np.array([r.get("archivo") or r["grupo_man"] for r in tren])
    pos_de = {(r["par"], r["rol"]): k for k, r in enumerate(tren)}
    ids_par = sorted({r["par"] for r in tren})
    pares = np.array([[pos_de[(p, "infiel")], pos_de[(p, "fiel")]] for p in ids_par])
    info_par = [tren[pos_de[(p, "infiel")]] for p in ids_par]
    info_fiel = [tren[pos_de[(p, "fiel")]] for p in ids_par]
    gp = g_origen[pares[:, 0]]
    ga = g[pares[:, 0]]
    n_pares, n_or, n_arch = len(pares), len(np.unique(gp)), len(np.unique(ga))
    print(f"{n_pares} pares en {n_or} orígenes y {n_arch} archivos; {len(tren)} filas de entrenamiento", flush=True)

    def X(v, pos):
        return R.acts(a.carpeta, v, pos, sel)

    out = dict(modelo=a.nombre, n_pares=n_pares, n_origenes=n_or, n_archivos=n_arch, semillas=list(semillas),
               n_perm=n_perm, agrupamiento_pliegues="archivo fuente")
    # textos (para superficie y superficie cruzada); el índice no guarda el texto: se lee del parquet
    import pyarrow.parquet as pq
    filas_pq = pq.read_table(os.path.join(os.path.dirname(a.indice), "pares_nivel_b.parquet")).to_pylist()
    lean_txt = [filas_pq[r["id"]]["autoformalization"] for r in tren]
    nl_txt = [filas_pq[r["id"]]["refined_statement"] for r in tren]
    pts, res = {}, {}
    for pos in ("ultimo", "media"):
        for v in ("completo", "solo_lean", "nl_desemparejado", "solo_nl"):
            p = ("media_nl" if v == "solo_nl" else "media_lean") if pos == "media" else "ultimo"
            res[v, pos] = R.correr_condicion(X(v, p), y, g, semillas, a.jobs)
            pts[v, pos], _ = R.puntajes(res[v, pos], len(y))
            print(f"  {v}/{pos}: AUROC_p {auc_p(pts[v, pos], pares, gp):.3f} ({time.time() - t0:.0f} s)", flush=True)

    c, l = pts["completo", "ultimo"], pts["solo_lean", "ultimo"]
    central = boot_p([c, l], pares, gp)
    out["central"] = dict(completo=central[0], solo_lean=central[1], diferencia=central[2])
    nulo = permutaciones({"completo": X("completo", "ultimo"), "solo_lean": X("solo_lean", "ultimo")},
                         y, g, pares, gp, n_perm, a.jobs)
    obs0 = {"completo": auc_p(R.puntajes(res["completo", "ultimo"], len(y))[1][0], pares, gp),
            "solo_lean": auc_p(R.puntajes(res["solo_lean", "ultimo"], len(y))[1][0], pares, gp)}
    obs0["diferencia"] = obs0["completo"] - obs0["solo_lean"]
    out["permutaciones"] = {k: dict(observado_semilla0=obs0[k], p=R.p_perm(nulo[k], obs0[k]),
                                    nulo_media=float(nulo[k].mean())) for k in nulo}
    # control 6 (superficie cruzada NL–Lean): es CONDICIÓN del positivo (revisor Fable, 2026-11-04):
    # el IC de completo − cruzada no puede quedar entero por debajo de 0.
    F = np.array([rasgos_cruzados(n, le) for n, le in zip(nl_txt, lean_txt)], dtype=float)
    cru = cruzada(F, y, g, semillas)
    cruz = boot_p([c, cru], pares, gp)
    # decisión
    ic_pos = central[2][1] > 0
    cruzada_ok = cruz[2][2] > 0  # el IC superior de (completo − cruzada) está por encima de 0
    if n_pares < a.umbral_minimo:
        dec = f"NO SE DECIDE: {n_pares} pares < umbral mínimo {a.umbral_minimo}"
    elif ic_pos and not cruzada_ok:
        dec = (f"NULO (condición 6): completo − solo_lean positivo pero completo − superficie cruzada "
               f"entero por debajo de 0 [{cruz[2][1]:.3f}; {cruz[2][2]:.3f}]")
    elif ic_pos:
        llena = n_pares >= a.umbral_pares and n_or >= a.umbral_origenes
        dec = "POSITIVO" + ("" if llena else f" (potencia reducida: {n_pares} pares, {n_or} orígenes; "
                                              f"umbrales {a.umbral_pares} y {a.umbral_origenes})")
    else:
        dec = f"NULO: no detectable con este tamaño; cota superior de la diferencia {central[2][2]:.3f}"
    out["decision"] = dec

    # secundarios y controles
    sec = {}
    sec["central_bootstrap_por_archivo"] = dict(zip(("completo", "solo_lean", "diferencia"), boot_p([c, l], pares, ga)),
                                                nota="sensibilidad: unidad de remuestreo = archivo fuente")
    sec["media_lean"] = dict(zip(("completo", "solo_lean", "diferencia"),
                                 boot_p([pts["completo", "media"], pts["solo_lean", "media"]], pares, gp)))
    for v in ("nl_desemparejado", "solo_nl"):
        sec[v] = boot_p([pts[v, "ultimo"]], pares, gp)[0]
    sup, _ = R.superficie(lean_txt, nl_txt, y, g, semillas, True, a.jobs)
    sec["superficie"] = dict(zip(("completo", "superficie", "diferencia"), boot_p([c, sup], pares, gp)))
    sec["superficie_cruzada"] = dict(zip(("completo", "cruzada", "diferencia"), cruz), condicion_del_positivo=True)
    py = np.load(os.path.join(a.carpeta, "pyes_completo.npy"))[sel]
    pyes = py[:, 4] / np.maximum(py[:, 4] + py[:, 5], 1e-12)
    sec["p_yes"] = dict(zip(("completo", "p_yes", "diferencia"), boot_p([c, pyes], pares, gp)),
                        masa_media=float((py[:, 4] + py[:, 5]).mean()))

    def sub(mask, nombre):
        m = np.array(mask)
        if m.sum() < 10:
            sec[nombre] = dict(n_pares=int(m.sum()), nota="menos de 10 pares; no se reporta")
            return
        r = boot_p([c, l], pares[m], gp[m])
        sec[nombre] = dict(n_pares=int(m.sum()), completo=r[0], solo_lean=r[1], diferencia=r[2],
                           p_yes=boot_p([pyes], pares[m], gp[m])[0])
    for fam in ("A", "B", "C"):
        sub([i["familia"] == fam for i in info_par], f"familia_{fam}")
    sub([(i.get("verdad_variante") or "").startswith("verdadera") for i in info_par], "verdad_infiel_verdadera")
    sub([(i.get("verdad_variante") or "").startswith("falsa") for i in info_par], "verdad_infiel_refutada")
    # control 8 por zona (revisor): las B verdaderas son casi todas de hipótesis y las A/C refutadas de
    # conclusión; se reporta el contraste dentro de cada zona para no confundir verdad con zona
    for z in ("hipotesis", "conclusion"):
        sub([(i.get("verdad_variante") or "").startswith("verdadera") and i["zona"] == z for i in info_par],
            f"verdad_infiel_verdadera_{z}")
        sub([(i.get("verdad_variante") or "").startswith("falsa") and i["zona"] == z for i in info_par],
            f"verdad_infiel_refutada_{z}")
    sub([not i["regla"].startswith("C2") for i in info_par], "sin_C2")
    sub([bool(i.get("base_fiel")) for i in info_par], "pares_compuestos")
    sub([f["regla"] not in RENOMBRES for f in info_fiel], "sin_renombres")
    sub([bool(set(i["objeto"]) & set(f["objeto"])) for i, f in zip(info_par, info_fiel)], "mismo_objeto")
    sub([i.get("nivel") == 2 for i in info_par], "nivel_2")
    sub([abs(f["tokens_editados"] - i["tokens_editados"]) <= 1 for i, f in zip(info_par, info_fiel)],
        "delta_tokens_max_1")
    sub([i["zona"] == f["zona"] for i, f in zip(info_par, info_fiel)], "misma_zona")
    for fu in sorted({i["fuente"] for i in info_par}):
        sub([i["fuente"] == fu for i in info_par], f"fuente_{fu}")
    for b in sorted({i["bin_edicion"] for i in info_par}):
        sub([i["bin_edicion"] == b for i in info_par], f"tokens_{b}")
    dt_ = np.array([f["tokens_editados"] - i["tokens_editados"] for i, f in zip(info_par, info_fiel)], float)
    ds = c[pares[:, 1]] - c[pares[:, 0]]
    sec["pendiente_dpuntaje_dtokens"] = float(np.polyfit(dt_, ds, 1)[0]) if dt_.std() > 0 else None
    # original frente a fiel
    sel_o = np.array([r["fila"] for r in orig])
    g_o = np.array([r["grupo_man"] for r in orig])
    # Desviación (6 nov 2026, 06:1x): los pliegues se agrupan por ARCHIVO (g); el original se busca en
    # el fold por su archivo, no por el hash del NL (antes nunca coincidía y el control daba 0,0).
    a_o = np.array([r.get("archivo") or r["grupo_man"] for r in orig])
    s_o = puntuar_originales(res["completo", "ultimo"], X("completo", "ultimo"), y, g,
                             R.acts(a.carpeta, "completo", "ultimo", sel_o), a_o)
    so_por_g = dict(zip(g_o, s_o))
    w = np.array([1.0 if so_por_g[gg] > c[f] else (0.5 if so_por_g[gg] == c[f] else 0.0)
                  for gg, f in zip(gp, pares[:, 1])])
    sec["original_vs_fiel"] = dict(p_original_mayor=float(por_origen(w, gp).mean()),
                                   nota="≈ 0,5 si «haber sido editado» no es la señal")
    out["secundarios"] = sec
    out["segundos"] = round(time.time() - t0, 1)
    os.makedirs(a.salida, exist_ok=True)
    sufijo = "_rapido" if a.rapido else ""
    json.dump(out, open(os.path.join(a.salida, f"nivel_b_{a.nombre}{sufijo}.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)
    L = [f"# Nivel B — {a.nombre}{' (rápido: NO usar)' if a.rapido else ''}", "",
         f"{n_pares} pares certificados en {n_or} orígenes y {n_arch} archivos (pliegues por archivo). Decisión: **{dec}**", "",
         f"- AUROC pareada completo {fmt(central[0])}; solo Lean {fmt(central[1])}; diferencia {fmt(central[2])}",
         f"- Permutaciones dentro del par ({n_perm}): p completo = {out['permutaciones']['completo']['p']:.4f}; "
         f"p diferencia = {out['permutaciones']['diferencia']['p']:.4f}"]
    for k, v in sec.items():
        L.append(f"- {k}: {json.dumps(v, ensure_ascii=False)}")
    open(os.path.join(a.salida, f"nivel_b_{a.nombre}{sufijo}.md"), "w", encoding="utf-8").write("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
