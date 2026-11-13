"""EXPLORATORIO, POST HOC (6 nov 2026): desglose por familia de la infiel (A, B, C; y C2 frente a C3)
del control «completo − superficie cruzada NL–Lean» del análisis pareado principal del Nivel B.
Pedido después de ver los resultados; no forma parte de la regla de decisión.

Reutiliza las funciones de analizar_pares.py y probe_referencia.py sin modificarlas: mismos puntajes OOF
de «completo» (posición «ultimo», capa por CV anidada, 5 semillas, pliegues por archivo) y de la
superficie cruzada (rasgos_cruzados), mismo estadístico (auc_p) y mismo bootstrap de orígenes (boot_p,
2000, semilla 0).

Uso: nice -n 10 biblioteca/.venv/bin/python -I probes/nivel_b/superficie_cruzada_por_familia.py --jobs 4
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse
import json
import sys
import time

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import analizar_pares as AP  # noqa: E402
R = AP.R


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--carpeta", default=os.path.join(os.path.dirname(AQUI), "activaciones", "nivel_b_qwen3_4b"))
    ap.add_argument("--indice", default=os.path.join(AQUI, "datos", "pares_indice_principal.jsonl"))
    ap.add_argument("--jobs", type=int, default=4)
    a = ap.parse_args()
    t0 = time.time()

    # --- misma construcción que analizar_pares.main()
    man = [json.loads(l) for l in open(os.path.join(a.carpeta, "manifiesto.jsonl"), encoding="utf-8")]
    ind = {r["id"]: r for r in map(json.loads, open(a.indice, encoding="utf-8"))}
    filas = [dict(ind[m["id"]], fila=j, grupo_man=m["grupo"]) for j, m in enumerate(man) if m["id"] in ind]
    tren = [r for r in filas if r["rol"] in ("infiel", "fiel")]
    sel = np.array([r["fila"] for r in tren])
    y = np.array([int(r["rol"] == "fiel") for r in tren])
    g_origen = np.array([r["grupo_man"] for r in tren])
    g = np.array([r.get("archivo") or r["grupo_man"] for r in tren])
    pos_de = {(r["par"], r["rol"]): k for k, r in enumerate(tren)}
    ids_par = sorted({r["par"] for r in tren})
    pares = np.array([[pos_de[(p, "infiel")], pos_de[(p, "fiel")]] for p in ids_par])
    info_par = [tren[pos_de[(p, "infiel")]] for p in ids_par]
    gp = g_origen[pares[:, 0]]
    print(f"{len(pares)} pares en {len(np.unique(gp))} orígenes", flush=True)

    import pyarrow.parquet as pq
    filas_pq = pq.read_table(os.path.join(os.path.dirname(a.indice), "pares_nivel_b.parquet")).to_pylist()
    lean_txt = [filas_pq[r["id"]]["autoformalization"] for r in tren]
    nl_txt = [filas_pq[r["id"]]["refined_statement"] for r in tren]

    semillas = R.SEMILLAS
    res = R.correr_condicion(R.acts(a.carpeta, "completo", "ultimo", sel), y, g, semillas, a.jobs)
    c, _ = R.puntajes(res, len(y))
    print(f"completo/ultimo: AUROC_p {AP.auc_p(c, pares, gp):.3f} ({time.time() - t0:.0f} s)", flush=True)
    F = np.array([AP.rasgos_cruzados(n, le) for n, le in zip(nl_txt, lean_txt)], dtype=float)
    cru = AP.cruzada(F, y, g, semillas)

    glob = AP.boot_p([c, cru], pares, gp)
    out = dict(rotulo="EXPLORATORIO, POST HOC: análisis adicional pedido después de ver los resultados",
               indice=os.path.relpath(a.indice, AQUI), carpeta=os.path.relpath(a.carpeta, AQUI),
               semillas=list(semillas), n_boot=AP.N_BOOT, semilla_boot=0, unidad_bootstrap="origen",
               global_=dict(n_pares=len(pares), completo=glob[0], cruzada=glob[1], diferencia=glob[2]))
    ref = dict(completo=0.807, cruzada=0.688)
    ok = abs(glob[0][0] - ref["completo"]) <= 0.005 and abs(glob[1][0] - ref["cruzada"]) <= 0.005
    out["reproduce_global"] = dict(referencia=ref, ok=bool(ok))
    print(f"global: completo {AP.fmt(glob[0])}; cruzada {AP.fmt(glob[1])}; dif {AP.fmt(glob[2])}; reproduce={ok}")
    if not ok:
        json.dump(out, open(os.path.join(AQUI, "resultados", "superficie_cruzada_por_familia.json"), "w",
                       encoding="utf-8"), ensure_ascii=False, indent=1)
        sys.exit("No reproduce las cifras globales; me detengo.")

    # descriptivo: ¿la infiel tiene más numerales del Lean ausentes del NL que la fiel? (F[:,0])
    dnum = F[pares[:, 0], 0] - F[pares[:, 1], 0]

    subgrupos = {"familia_A": [i["familia"] == "A" for i in info_par],
                 "familia_B": [i["familia"] == "B" for i in info_par],
                 "familia_C": [i["familia"] == "C" for i in info_par],
                 "C2": [i["regla"].startswith("C2") for i in info_par],
                 "C3": [i["regla"].startswith("C3") for i in info_par]}
    out["subgrupos"] = {}
    for k, mask in subgrupos.items():
        m = np.array(mask)
        r = AP.boot_p([c, cru], pares[m], gp[m])
        out["subgrupos"][k] = dict(n_pares=int(m.sum()), n_origenes=int(len(np.unique(gp[m]))),
                                   completo=r[0], cruzada=r[1], diferencia=r[2],
                                   ic_entero_sobre_0=bool(r[2][1] > 0),
                                   frac_pares_infiel_con_mas_numerales_ausentes_del_nl=float((dnum[m] > 0).mean()))
        print(f"{k} ({m.sum()} pares): completo {AP.fmt(r[0])}; cruzada {AP.fmt(r[1])}; dif {AP.fmt(r[2])}", flush=True)
    out["segundos"] = round(time.time() - t0, 1)
    json.dump(out, open(os.path.join(AQUI, "resultados", "superficie_cruzada_por_familia.json"), "w",
                   encoding="utf-8"), ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
