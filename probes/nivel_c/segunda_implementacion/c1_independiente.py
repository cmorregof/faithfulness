"""Segunda implementación independiente de la prueba C1 del Nivel C (regla_borrador.md §3, §4 y C1-dentro).

Escrita desde cero sin leer probe_c.py, probes/referencia/ ni probes/probe.py.

Uso:
  OMP_NUM_THREADS=1 nice -n 10 python -I c1_independiente.py [--capas 0,18,36] [--semillas 0,1] [--salida X.json]

Diseño:
  - probe: StandardScaler (ajustado en entrenamiento) + LogisticRegression(L2, C=1, lbfgs).
  - externas: StratifiedGroupKFold(5, shuffle=True, random_state=s), s en 0..4, grupos = `grupo`.
    Las particiones dependen solo de (y, grupo, s), así que son idénticas en ambas condiciones.
  - capa: CV anidada en cada fold externo, StratifiedGroupKFold(5, shuffle=True, random_state=s)
    sobre el entrenamiento; criterio = AUROC de los OOF internos concatenados; empate -> capa más baja.
  - puntaje por fila: OOF (predict_proba) promediado entre semillas.
  - Δ = AUROC(completo) - AUROC(solo_lean); IC 95 % por bootstrap de grupos estratificado por
    tipo de grupo (2000, semilla 0); Δ dentro de grupo con bootstrap de grupos mixtos.
"""
import argparse
import json
import os
import time
from collections import defaultdict
from pathlib import Path

import numpy as np
from joblib import Parallel, delayed
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import roc_auc_score
from sklearn.model_selection import StratifiedGroupKFold
from sklearn.preprocessing import StandardScaler

BASE = Path(__file__).resolve().parent.parent
ACTS = BASE / "activaciones" / "qwen3_4b_proofnetverif"
AQUI = Path(__file__).resolve().parent
CONDICIONES = ["completo", "solo_lean"]
N_BOOT = 2000


def cargar_manifiesto():
    filas = [json.loads(l) for l in open(ACTS / "manifiesto.jsonl")]
    assert all(f["idx"] == i for i, f in enumerate(filas))
    y = np.array([f["etiqueta"] for f in filas], dtype=int)
    g = np.array([f["grupo"] for f in filas])
    return y, g


def ajustar_y_puntuar(Xtr, ytr, Xte):
    esc = StandardScaler().fit(Xtr)
    m = LogisticRegression(C=1.0, max_iter=20000).fit(esc.transform(Xtr), ytr)
    Z = esc.transform(Xte)
    return m.predict_proba(Z)[:, 1], m.decision_function(Z), int(m.n_iter_[0])


def fold_externo(cond, semilla, k, tr, te, y, g, capas):
    A = np.load(ACTS / f"acts_{cond}_ultimo.npy", mmap_mode="r")
    ytr, gtr = y[tr], g[tr]
    interna = list(StratifiedGroupKFold(5, shuffle=True, random_state=semilla).split(np.zeros(len(tr)), ytr, gtr))
    auc_int = []
    max_iter = 0
    for L in capas:
        X = np.asarray(A[tr, L, :], dtype=np.float64)
        oof = np.full(len(tr), np.nan)
        for itr, ite in interna:
            p, _, it = ajustar_y_puntuar(X[itr], ytr[itr], X[ite])
            oof[ite] = p
            max_iter = max(max_iter, it)
        auc_int.append(roc_auc_score(ytr, oof))
    auc_int = np.array(auc_int)
    j = int(np.flatnonzero(auc_int == auc_int.max())[0])  # empate -> capa más baja
    capa = capas[j]
    Xtr = np.asarray(A[tr, capa, :], dtype=np.float64)
    Xte = np.asarray(A[te, capa, :], dtype=np.float64)
    p, d, it = ajustar_y_puntuar(Xtr, ytr, Xte)
    return dict(cond=cond, semilla=semilla, fold=k, te=te, p=p, d=d, capa=int(capa),
                auc_interno=auc_int.tolist(), max_iter=max(max_iter, it))


def tipos_grupo(y, g):
    acc = defaultdict(list)
    for yi, gi in zip(y, g):
        acc[gi].append(yi)
    t = {}
    for gi, v in acc.items():
        s = sum(v)
        t[gi] = "mixto" if 0 < s < len(v) else ("solo_pos" if s else "solo_neg")
    return t


def auc_dentro(y, g, s, grupos_mixtos, idx_por_grupo):
    """Fracción de pares (pos, neg) del mismo grupo con pos > neg; empates ½. Agregado sobre pares."""
    num = 0.0
    den = 0
    por_grupo = []
    for gi in grupos_mixtos:
        ii = idx_por_grupo[gi]
        sp = s[ii][y[ii] == 1]
        sn = s[ii][y[ii] == 0]
        dif = sp[:, None] - sn[None, :]
        c = (dif > 0).sum() + 0.5 * (dif == 0).sum()
        num += c
        den += dif.size
        por_grupo.append((c, dif.size))
    return num / den, np.array(por_grupo, dtype=float)


def resumen(y, g, sa, sb, semilla_boot=0):
    tipo = tipos_grupo(y, g)
    idx_por_grupo = defaultdict(list)
    for i, gi in enumerate(g):
        idx_por_grupo[gi].append(i)
    idx_por_grupo = {k: np.array(v) for k, v in idx_por_grupo.items()}
    estratos = {t: sorted(k for k in idx_por_grupo if tipo[k] == t) for t in ["solo_pos", "solo_neg", "mixto"]}

    auc_a, auc_b = roc_auc_score(y, sa), roc_auc_score(y, sb)
    rng = np.random.default_rng(semilla_boot)
    boot = np.empty((N_BOOT, 3))
    for b in range(N_BOOT):
        partes = []
        for t in ["solo_pos", "solo_neg", "mixto"]:
            gs = estratos[t]
            elegidos = rng.integers(0, len(gs), len(gs))
            partes.extend(idx_por_grupo[gs[e]] for e in elegidos)
        ii = np.concatenate(partes)
        a, bb = roc_auc_score(y[ii], sa[ii]), roc_auc_score(y[ii], sb[ii])
        boot[b] = (a, bb, a - bb)

    mixtos = estratos["mixto"]
    da, pga = auc_dentro(y, g, sa, mixtos, idx_por_grupo)
    db, pgb = auc_dentro(y, g, sb, mixtos, idx_por_grupo)
    rng2 = np.random.default_rng(semilla_boot)
    bd = np.empty((N_BOOT, 3))
    for b in range(N_BOOT):
        e = rng2.integers(0, len(mixtos), len(mixtos))
        a = pga[e, 0].sum() / pga[e, 1].sum()
        bb = pgb[e, 0].sum() / pgb[e, 1].sum()
        bd[b] = (a, bb, a - bb)
    # variante: media de AUROC por grupo (no la de la regla; solo informativa)
    media_a = float(np.mean(pga[:, 0] / pga[:, 1]))
    media_b = float(np.mean(pgb[:, 0] / pgb[:, 1]))

    ic = lambda v: [float(np.percentile(v, 2.5)), float(np.percentile(v, 97.5))]
    return dict(
        principal=dict(auroc_completo=float(auc_a), ic_completo=ic(boot[:, 0]),
                       auroc_solo_lean=float(auc_b), ic_solo_lean=ic(boot[:, 1]),
                       delta=float(auc_a - auc_b), ic_delta=ic(boot[:, 2]),
                       ee_delta_boot=float(boot[:, 2].std(ddof=1)),
                       n_grupos_por_estrato={t: len(v) for t, v in estratos.items()}),
        dentro_de_grupo=dict(auroc_completo=float(da), ic_completo=ic(bd[:, 0]),
                             auroc_solo_lean=float(db), ic_solo_lean=ic(bd[:, 1]),
                             delta=float(da - db), ic_delta=ic(bd[:, 2]),
                             n_grupos_mixtos=len(mixtos), n_pares=int(pga[:, 1].sum()),
                             variante_media_por_grupo=dict(completo=media_a, solo_lean=media_b,
                                                           delta=media_a - media_b)),
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--capas", default="all")
    ap.add_argument("--semillas", default="0,1,2,3,4")
    ap.add_argument("--n_jobs", type=int, default=2)
    ap.add_argument("--salida", default=str(AQUI / "resultado_c1.json"))
    args = ap.parse_args()

    y, g = cargar_manifiesto()
    n_capas = np.load(ACTS / "acts_completo_ultimo.npy", mmap_mode="r").shape[1]
    capas = list(range(n_capas)) if args.capas == "all" else [int(c) for c in args.capas.split(",")]
    semillas = [int(s) for s in args.semillas.split(",")]

    tareas = []
    particiones = {}
    for s in semillas:
        parts = list(StratifiedGroupKFold(5, shuffle=True, random_state=s).split(np.zeros(len(y)), y, g))
        # comprobaciones: cada fila sale una vez; ningún grupo cruza train/test
        cuenta = np.zeros(len(y), int)
        for tr, te in parts:
            cuenta[te] += 1
            assert not set(g[tr]) & set(g[te])
        assert (cuenta == 1).all()
        particiones[s] = parts
        for cond in CONDICIONES:
            for k, (tr, te) in enumerate(parts):
                tareas.append((cond, s, k, tr, te))

    t0 = time.time()
    res = Parallel(n_jobs=args.n_jobs, verbose=10)(
        delayed(fold_externo)(c, s, k, tr, te, y, g, capas) for c, s, k, tr, te in tareas)
    seg = time.time() - t0

    oof = {(c, s): np.full(len(y), np.nan) for c in CONDICIONES for s in semillas}
    oof_d = {(c, s): np.full(len(y), np.nan) for c in CONDICIONES for s in semillas}
    capas_elegidas = defaultdict(list)
    auc_int = defaultdict(list)
    max_iter = 0
    for r in sorted(res, key=lambda r: (r["cond"], r["semilla"], r["fold"])):
        oof[(r["cond"], r["semilla"])][r["te"]] = r["p"]
        oof_d[(r["cond"], r["semilla"])][r["te"]] = r["d"]
        capas_elegidas[r["cond"]].append(r["capa"])
        auc_int[r["cond"]].append(r["auc_interno"])
        max_iter = max(max_iter, r["max_iter"])
    assert all(np.isfinite(v).all() for v in oof.values())

    prom = {c: np.mean([oof[(c, s)] for s in semillas], axis=0) for c in CONDICIONES}
    prom_d = {c: np.mean([oof_d[(c, s)] for s in semillas], axis=0) for c in CONDICIONES}
    out = resumen(y, g, prom["completo"], prom["solo_lean"])

    por_semilla = []
    for s in semillas:
        a = roc_auc_score(y, oof[("completo", s)])
        b = roc_auc_score(y, oof[("solo_lean", s)])
        por_semilla.append(dict(semilla=s, auroc_completo=a, auroc_solo_lean=b, delta=a - b))
    deltas = np.array([d["delta"] for d in por_semilla])
    out["por_semilla"] = por_semilla
    out["dispersion_delta_semillas"] = dict(media=float(deltas.mean()),
                                           de=float(deltas.std(ddof=1)) if len(deltas) > 1 else None,
                                           min=float(deltas.min()), max=float(deltas.max()))
    # sensibilidad: promediar logits en vez de probabilidades
    sens = resumen(y, g, prom_d["completo"], prom_d["solo_lean"])
    out["sensibilidad_promedio_logits"] = dict(delta=sens["principal"]["delta"], ic_delta=sens["principal"]["ic_delta"],
                                               delta_dentro=sens["dentro_de_grupo"]["delta"],
                                               ic_delta_dentro=sens["dentro_de_grupo"]["ic_delta"])
    out["capas"] = {c: dict(elegidas_por_fold=capas_elegidas[c],
                            auc_interno_medio_por_capa=dict(zip(map(str, capas), np.mean(auc_int[c], axis=0).round(4).tolist())))
                    for c in CONDICIONES}
    out["config"] = dict(capas_candidatas=capas, semillas=semillas, n_filas=int(len(y)), n_pos=int(y.sum()),
                         n_grupos=int(len(set(g))), probe="StandardScaler + LogisticRegression(C=1, lbfgs, L2, max_iter=20000)",
                         puntaje="predict_proba promediado entre semillas", posicion="ultimo",
                         bootstrap=dict(n=N_BOOT, semilla=0, estratos="solo_pos, solo_neg, mixto; percentil 2,5/97,5"),
                         max_n_iter_observado=max_iter, segundos=round(seg, 1))
    Path(args.salida).write_text(json.dumps(out, ensure_ascii=False, indent=1))
    np.savez(Path(args.salida).with_suffix(".npz"), y=y, g=g,
             **{f"oof_{c}_s{s}": oof[(c, s)] for c in CONDICIONES for s in semillas})
    print(json.dumps({k: out[k] for k in ["principal", "dentro_de_grupo", "dispersion_delta_semillas"]}, indent=1))
    print("capas:", {c: capas_elegidas[c] for c in CONDICIONES}, "seg:", round(seg))


if __name__ == "__main__":
    main()
