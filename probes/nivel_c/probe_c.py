"""Nivel C: probes de referencia sobre un conjunto con etiquetas de otra fuente (ProofNetVerif).

Implementa probes/nivel_c/regla_borrador.md. NO CORRE sobre datos reales si no existe
probes/nivel_c/APROBADO_regla_decision (la crea solo Carlos). Reutiliza, sin modificarlas, las
funciones de probes/referencia/probe_referencia.py (probe, CV anidada, superficie, apilado,
permutaciones).

Análisis:
  C1 (principal)  CV agrupada dentro de ProofNetVerif: AUROC(completo) − AUROC(solo_lean),
                  último token, todas las filas; IC por bootstrap de grupos estratificado por tipo
                  de grupo (solo positivas / solo negativas / mixto).
  C1-dentro       la misma diferencia con AUROC dentro de grupo (pares positiva-negativa del mismo
                  enunciado), bootstrap de los grupos mixtos.
  C2 (transfer.)  probe entrenado en CriticLeanBench (450 que compilan; capa elegida SOLO con CV
                  en CriticLeanBench) y evaluado en ProofNetVerif; misma diferencia.
  Controles       solo_nl, nl_desemparejado, apilado, misma capa, media_lean, superficie,
                  P(Yes), permutaciones.

Uso:
  biblioteca/.venv/bin/python -I probes/nivel_c/probe_c.py \
      --carpeta probes/nivel_c/activaciones/qwen3_4b_proofnetverif \
      --carpeta_cl probes/activaciones/qwen3_4b --nombre qwen3_4b
  --sintetico: datos falsos pequeños (sin marca de aprobación; solo prueba que el código corre)
"""

import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse
import datetime as dt
import importlib.util
import json
import sys
import time

import numpy as np
import pyarrow.parquet as pq
from sklearn.model_selection import StratifiedGroupKFold

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(os.path.dirname(AQUI))
MARCA = os.path.join(AQUI, "APROBADO_regla_decision")
DATOS_C = os.path.join(AQUI, "datos_proc", "proofnetverif.parquet")
DATOS_CL = os.path.join(RAIZ, "probes", "datos", "criticleanbench_test.parquet")

_spec = importlib.util.spec_from_file_location(
    "probe_referencia", os.path.join(RAIZ, "probes", "referencia", "probe_referencia.py"))
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

SEMILLAS = ref.SEMILLAS          # 0–4, igual que la regla de las 12:55
N_BOOT = ref.N_BOOT              # 2000
N_PERM_C = 20                    # regla_borrador.md, sección 6 (costo ×8 respecto a CriticLeanBench)


# ------------------------------------------------------------ bootstrap con grupos mixtos

def tipos_de_grupo(y, g):
    tipo = {}
    for k in np.unique(g):
        e = set(y[g == k].tolist())
        tipo[k] = "mixto" if len(e) == 2 else ("pos" if e == {1} else "neg")
    return tipo


def auc_dentro(y, g, s):
    """AUROC dentro de grupo: fracción de pares (positiva, negativa) del MISMO grupo en que la
    positiva tiene mayor puntaje (empates = 1/2). Solo cuentan los grupos mixtos."""
    num, den = 0.0, 0
    for k in np.unique(g):
        m = g == k
        sp, sn = s[m & (y == 1)], s[m & (y == 0)]
        if len(sp) == 0 or len(sn) == 0:
            continue
        d = sp[:, None] - sn[None, :]
        num += float((d > 0).sum() + 0.5 * (d == 0).sum())
        den += d.size
    return num / den if den else float("nan")


def bootstrap_c(y, g, puntajes, n=None, semilla=0, dentro=False):
    """IC 95 % por bootstrap de grupos estratificado por tipo de grupo (pos/neg/mixto).

    dentro=False: AUROC global sobre las filas de los grupos elegidos.
    dentro=True:  AUROC dentro de grupo; solo se remuestrean los grupos mixtos.
    Devuelve (puntual, lo, hi) por vector y, si hay dos, también de la diferencia [0] − [1].
    Los grupos repetidos en un remuestreo se tratan como grupos distintos (se re-etiquetan).
    """
    n = ref.N_BOOT if n is None else n
    rng = np.random.default_rng(semilla)
    tipo = tipos_de_grupo(y, g)
    filas = {k: np.flatnonzero(g == k) for k in tipo}
    estratos = ["mixto"] if dentro else ["pos", "neg", "mixto"]
    por_estrato = {t: np.array([k for k in tipo if tipo[k] == t]) for t in estratos}
    medir = (lambda yy, gg, ss: auc_dentro(yy, gg, ss)) if dentro else (lambda yy, gg, ss: ref.auc(yy, ss))
    reps = []
    for _ in range(n):
        elegidos = np.concatenate([rng.choice(v, len(v)) for v in por_estrato.values() if len(v)])
        idx = np.concatenate([filas[k] for k in elegidos])
        gg = np.concatenate([np.full(len(filas[k]), j) for j, k in enumerate(elegidos)])
        if len(np.unique(y[idx])) < 2:
            continue
        reps.append([medir(y[idx], gg, s[idx]) for s in puntajes])
    reps = np.array(reps)
    out = []
    for j, s in enumerate(puntajes):
        lo, hi = np.percentile(reps[:, j], [2.5, 97.5])
        out.append((medir(y, g, s), float(lo), float(hi)))
    if len(puntajes) == 2:
        d = reps[:, 0] - reps[:, 1]
        lo, hi = np.percentile(d, [2.5, 97.5])
        out.append((out[0][0] - out[1][0], float(lo), float(hi)))
    return out


def dif(y, g, a, b, dentro=False):
    r = bootstrap_c(y, g, [a, b], dentro=dentro)
    return {"a": {"auroc": r[0][0], "ic": [r[0][1], r[0][2]]},
            "b": {"auroc": r[1][0], "ic": [r[1][1], r[1][2]]},
            "diferencia": {"punto": r[2][0], "ic": [r[2][1], r[2][2]], "positivo": bool(r[2][1] > 0)}}


# ------------------------------------------------------------ transferencia

def capa_por_cv(X, y, g, semillas):
    """Capa elegida SOLO con el conjunto de entrenamiento: AUROC OOF por capa con
    StratifiedGroupKFold(5) para cada semilla, promedio entre semillas; empate -> la más baja."""
    L = X.shape[1]
    aucs = np.zeros((len(semillas), L))
    for i, s in enumerate(semillas):
        parts = ref.particiones(y, g, s)
        for c in range(L):
            oof = np.zeros(len(y))
            for tr, te in parts:
                oof[te] = ref.ajustar_predecir(X[tr, c], y[tr], X[te, c])
            aucs[i, c] = ref.auc(y, oof)
    media = aucs.mean(0)
    return int(np.flatnonzero(media == media.max())[0]), media


def transferir(Xtr, ytr, gtr, Xte, semillas):
    capa, curva = capa_por_cv(Xtr, ytr, gtr, semillas)
    pred = ref.ajustar_predecir(Xtr[:, capa], ytr, Xte[:, capa])
    # Todas las capas (solo para la figura; no se usan para decidir)
    por_capa = [ref.ajustar_predecir(Xtr[:, c], ytr, Xte[:, c]) for c in range(Xtr.shape[1])]
    return {"capa": capa, "curva_cv_entrenamiento": curva.tolist(), "pred": pred, "pred_por_capa": por_capa}


# ------------------------------------------------------------ datos

def cargar_c(carpeta):
    man = [json.loads(l) for l in open(os.path.join(carpeta, "manifiesto.jsonl"), encoding="utf-8")]
    meta = json.load(open(os.path.join(carpeta, "meta.json"), encoding="utf-8"))
    return man, meta


def datos_sinteticos(n_grupos=40, L=6, D=32, semilla=0):
    """Datos falsos con grupos mixtos, para probar el código (no dicen nada del modelo)."""
    rng = np.random.default_rng(semilla)
    g, y = [], []
    for k in range(n_grupos):
        m = rng.integers(2, 9)
        p = rng.uniform(0.05, 0.6)
        g += [f"g{k}"] * m
        y += (rng.random(m) < p).astype(int).tolist()
    g, y = np.array(g), np.array(y)
    n = len(y)
    base = rng.normal(size=(n, L, D))
    X = {}
    X["solo_lean"] = base + 0.3 * y[:, None, None] * (np.arange(D) == 0)
    X["completo"] = base + 0.6 * y[:, None, None] * (np.arange(D) == 0)
    X["solo_nl"] = rng.normal(size=(n, L, D))
    X["nl_desemparejado"] = base + 0.3 * y[:, None, None] * (np.arange(D) == 0)
    pyes = rng.random((n, 8)).astype(np.float32)
    lean = [f"theorem dummy (x : ℕ) : x + {i % 7} = {i % 5} := sorry" for i in range(n)]
    nl = [f"Show that statement {k} holds." for k in g]
    return y, g, X, pyes, lean, nl


# ------------------------------------------------------------ principal

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--carpeta", help="activaciones de ProofNetVerif (salida de extraer_c.py)")
    ap.add_argument("--carpeta_cl", default=os.path.join(RAIZ, "probes", "activaciones", "qwen3_4b"),
                    help="activaciones de CriticLeanBench del MISMO modelo (para C2)")
    ap.add_argument("--nombre", default="qwen3_4b")
    ap.add_argument("--salida", default=os.path.join(AQUI, "resultados"))
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--sintetico", action="store_true")
    a = ap.parse_args()
    t0 = time.time()

    if a.sintetico:
        semillas, n_perm, n_boot = (0, 1), 3, 200
        ref.N_BOOT = n_boot
        y, g, Xd, pyes_c, lean, nl = datos_sinteticos()
        acts_c = lambda v, pos: Xd[v] if pos == "ultimo" else Xd[v] * 0.5
        pyes = {v: pyes_c for v in Xd}
        yc, gc, Xcl = datos_sinteticos(semilla=1)[:3]
        acts_cl = lambda v: Xcl[v]
        meta = {"modelo": "sintetico", "revision": "-"}
        a.salida = os.path.join(AQUI, "prueba_sintetica")
    else:
        if not os.path.exists(MARCA):
            sys.exit(f"Me niego a correr: falta {os.path.relpath(MARCA, RAIZ)}. "
                     "La regla de decisión del Nivel C no está aprobada por Carlos.")
        semillas, n_perm = SEMILLAS, N_PERM_C
        man, meta = cargar_c(a.carpeta)
        faltan = [v for v in ("completo", "solo_lean", "solo_nl", "nl_desemparejado")
                  if v not in meta.get("variantes_completas", [])]
        if faltan:
            sys.exit(f"Extracción incompleta en {a.carpeta}: faltan {faltan}")
        idx = np.array([m["idx"] for m in man])
        y = np.array([m["etiqueta"] for m in man])
        g = np.array([m["grupo"] for m in man])
        filas = pq.read_table(DATOS_C).to_pylist()
        lean = [filas[i]["autoformalization"].strip() for i in idx]
        nl = [filas[i]["refined_statement"].strip() for i in idx]
        acts_c = lambda v, pos: ref.acts(a.carpeta, v, pos, idx)
        pyes = {v: np.load(os.path.join(a.carpeta, f"pyes_{v}.npy"))[idx]
                for v in ("completo", "solo_lean", "solo_nl", "nl_desemparejado")}
        man_cl = [json.loads(l) for l in open(os.path.join(a.carpeta_cl, "manifiesto.jsonl"), encoding="utf-8")]
        meta_cl = json.load(open(os.path.join(a.carpeta_cl, "meta.json"), encoding="utf-8"))
        if (meta_cl["modelo"], meta_cl["revision"]) != (meta["modelo"], meta["revision"]):
            sys.exit("CriticLeanBench y ProofNetVerif no son del mismo modelo/revisión")
        sel_cl = np.array([m["idx"] for m in man_cl if m["compila"] == 1])
        yc = np.array([m["etiqueta"] for m in man_cl if m["compila"] == 1])
        gc = np.array([m["grupo"] for m in man_cl if m["compila"] == 1])
        acts_cl = lambda v: ref.acts(a.carpeta_cl, v, "ultimo", sel_cl)

    n = len(y)
    tipo = tipos_de_grupo(y, g)
    R = {"modelo": meta["modelo"], "revision": meta["revision"],
         "fecha": dt.datetime.now().astimezone().isoformat(timespec="minutes"),
         "semillas": list(semillas), "n_perm": n_perm, "n_boot": ref.N_BOOT, "C": ref.C,
         "n": int(n), "n_pos": int(y.sum()), "n_grupos": len(tipo),
         "grupos_por_tipo": {t: sum(1 for v in tipo.values() if v == t) for t in ("pos", "neg", "mixto")}}

    def log(msg):
        print(f"[{time.time() - t0:.0f} s] {msg}", flush=True)

    # ---- C1: CV agrupada dentro del conjunto
    res, pts, sem = {}, {}, {}
    for v in ("completo", "solo_lean", "solo_nl", "nl_desemparejado"):
        X = acts_c(v, "ultimo")
        res[v] = ref.correr_condicion(X, y, g, semillas, a.jobs)
        pts[v], sem[v] = ref.puntajes(res[v], n)
        log(f"C1 {v}")
    C1 = {"principal": dif(y, g, pts["completo"], pts["solo_lean"])}
    C1["principal"]["por_semilla"] = [ref.auc(y, sem["completo"][s]) - ref.auc(y, sem["solo_lean"][s])
                                      for s in semillas]
    C1["dentro_de_grupo"] = dif(y, g, pts["completo"], pts["solo_lean"], dentro=True)
    for v in res:
        C1[f"auroc_{v}"] = {"auroc": bootstrap_c(y, g, [pts[v]])[0],
                            "dentro": auc_dentro(y, g, pts[v]),
                            "capas_elegidas": [r["mejor"] for s in res[v] for (_, _, r) in res[v][s]],
                            "curva_capas": ref.curva_capas(res[v], y)}
    C1["completo_vs_nl_desemparejado"] = dif(y, g, pts["completo"], pts["nl_desemparejado"])
    C1["completo_vs_nl_desemparejado_dentro"] = dif(y, g, pts["completo"], pts["nl_desemparejado"], dentro=True)
    misma, _ = ref.puntajes(res["solo_lean"], n, capa_de=res["completo"])
    C1["misma_capa"] = dif(y, g, pts["completo"], misma)
    apil, _ = ref.apilado(res["solo_lean"], res["solo_nl"], y, n)
    C1["completo_vs_apilado"] = dif(y, g, pts["completo"], apil)
    C1["completo_vs_apilado_dentro"] = dif(y, g, pts["completo"], apil, dentro=True)
    # media_lean (secundario)
    pm = {}
    for v in ("completo", "solo_lean"):
        r = ref.correr_condicion(acts_c(v, "media_lean"), y, g, semillas, a.jobs)
        pm[v], _ = ref.puntajes(r, n)
    C1["media_lean"] = dif(y, g, pm["completo"], pm["solo_lean"])
    log("C1 media_lean")
    # superficie
    for nombre, con_nl in (("superficie_lean", False), ("superficie_lean_mas_nl", True)):
        sp, _ = ref.superficie(lean, nl, y, g, semillas, con_nl, a.jobs)
        C1[f"completo_vs_{nombre}"] = dif(y, g, pts["completo"], sp)
        C1[f"completo_vs_{nombre}_dentro"] = dif(y, g, pts["completo"], sp, dentro=True)
    log("C1 superficie")
    # P(Yes)
    for v, q in pyes.items():
        masa = q[:, 4] + q[:, 5]
        py = q[:, 4] / np.maximum(masa, 1e-12)
        e = {"masa_media": float(masa.mean()), "interpretable": bool(masa.mean() >= 0.5)}
        if v == "completo":
            e.update(dif(y, g, pts["completo"], py))
        else:
            e["auroc"] = bootstrap_c(y, g, [py])[0]
        C1[f"pyes_{v}"] = e
    # permutaciones (control)
    Xp = {v: acts_c(v, "ultimo") for v in ("completo", "solo_lean")}
    nulo = ref.permutaciones(Xp, y, g, n_perm, a.jobs)
    obs0 = {v: ref.auc(y, sem[v][0]) for v in Xp}
    C1["permutaciones"] = {v: {"observado_semilla0": obs0[v], "nulo_max": float(nulo[v].max()),
                               "nulo_media": float(nulo[v].mean()), "p": ref.p_perm(nulo[v], obs0[v])}
                           for v in Xp}
    log("C1 permutaciones")
    R["C1"] = C1

    # ---- C2: transferencia CriticLeanBench -> ProofNetVerif
    C2, tp = {}, {}
    for v in ("completo", "solo_lean"):
        t = transferir(acts_cl(v), yc, gc, acts_c(v, "ultimo"), semillas)
        tp[v] = t["pred"]
        C2[f"capa_{v}"] = t["capa"]
        C2[f"curva_cv_cl_{v}"] = t["curva_cv_entrenamiento"]
        C2[f"auroc_por_capa_en_pnv_{v}"] = [ref.auc(y, p) for p in t["pred_por_capa"]]
        if v == "completo":
            # el probe de completo aplicado a nl_desemparejado de ProofNetVerif (misma capa)
            X_des = acts_c("nl_desemparejado", "ultimo")
            p_des = ref.ajustar_predecir(acts_cl("completo")[:, t["capa"]], yc, X_des[:, t["capa"]])
        log(f"C2 {v}")
    C2["principal"] = dif(y, g, tp["completo"], tp["solo_lean"])
    C2["dentro_de_grupo"] = dif(y, g, tp["completo"], tp["solo_lean"], dentro=True)
    C2["completo_vs_nl_desemparejado"] = dif(y, g, tp["completo"], p_des)
    C2["n_entrenamiento"] = int(len(yc))
    R["C2"] = C2
    R["segundos"] = round(time.time() - t0)

    os.makedirs(a.salida, exist_ok=True)
    # Puntajes OOF por fila (para los subconjuntos preespecificados de la regla §4 —por source, split
    # y tipo de grupo— y para comparar con la segunda implementación). No cambia ningún cálculo.
    np.savez(os.path.join(a.salida, f"puntajes_c_{a.nombre}{'_sintetico' if a.sintetico else ''}.npz"),
             y=y, g=g.astype(str), **{f"c1_{v}": pts[v] for v in pts}, c1_misma_capa=misma, c1_apilado=apil,
             **{f"c1_media_lean_{v}": pm[v] for v in pm}, **{f"c2_{v}": tp[v] for v in tp}, c2_completo_en_nl_desemparejado=p_des)
    ruta = os.path.join(a.salida, f"resultados_c_{a.nombre}{'_sintetico' if a.sintetico else ''}.json")
    with open(ruta, "w", encoding="utf-8") as fh:
        json.dump(R, fh, ensure_ascii=False, indent=1, default=float)
    log(f"listo: {ruta}")


if __name__ == "__main__":
    main()
