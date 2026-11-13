"""Prueba de punta a punta de analizar_pares.py con datos SINTÉTICOS (revisor Fable, 2026-11-04).

No usa modelos, ni Lean, ni activaciones reales: fabrica en una carpeta temporal un manifiesto, las
matrices de activaciones (ruido + señal artificial), P(Yes), el índice de pares y el parquet con el
esquema que escriben extraer_pares.py y probes/extraer.py, y llama a analizar_pares.main() con
--prueba --rapido. Solo comprueba que el código corre y que las salidas tienen la forma esperada;
los números no dicen nada del modelo.

Uso: OMP_NUM_THREADS=2 biblioteca/.venv/bin/python -I probes/nivel_b/probar_analizar_sintetico.py [--carpeta DIR] [--jobs 2]
"""
import argparse
import json
import os
import sys
import tempfile

import numpy as np
import pyarrow as pa
import pyarrow.parquet as pq

AQUI = os.path.dirname(os.path.abspath(__file__))


def fabricar(carpeta, n_origenes=48, L=4, D=12, semilla=0):
    rng = np.random.default_rng(semilla)
    rows, acts_rows = [], []
    k_par = 0
    for o in range(n_origenes):
        arch = f"Archivo/{o // 3}"  # tres orígenes por archivo: prueba el agrupamiento por archivo
        nl = f"Statement number {o}: for all x at least {o % 7} the bound holds."
        rows.append(dict(rol="original", id_origen=f"o{o}", archivo=arch, par=None, regla="original", familia="O",
                         nl=nl, lean=f"theorem t{o} (x : ℕ) (h : {o % 7} ≤ x) : x + 1 ≤ x + 2 := by\n  sorry", tag="compile_right_is_right"))
        for j in range(1 + (o % 2)):
            fam = ["A", "B", "C"][(o + j) % 3]
            zona = ["hipotesis", "conclusion"][(o + j) % 2]
            verdad = {"A": "falsa (refutada)", "B": "verdadera si el original lo es (dirección O⇒V probada)", "C": "desconocida"}[fam]
            rows.append(dict(rol="infiel", id_origen=f"o{o}", archivo=arch, par=k_par, regla=f"{fam}3∘D1", familia=fam,
                             zona=zona, objeto=["relacion"], tokens_editados=5, bin_edicion="5-8", nivel=2,
                             verdad_variante=verdad, fuente="sintetico", base_fiel=f"o{o}::D1", nl=nl,
                             lean=f"theorem t{o} (x : ℕ) (h : x ≥ {o % 7 + 1}) : x + 1 ≤ x + 2 := by\n  sorry",
                             tag="compile_right_is_false"))
            rows.append(dict(rol="fiel", id_origen=f"o{o}", archivo=arch, par=k_par, regla="D1", familia="D",
                             zona=zona, objeto=["relacion"], tokens_editados=4, bin_edicion="1-4", nivel=None,
                             verdad_variante="igual a la del original", fuente="sintetico", nl=nl,
                             lean=f"theorem t{o} (x : ℕ) (h : x ≥ {o % 7}) : x + 1 ≤ x + 2 := by\n  sorry",
                             tag="compile_right_is_right"))
            k_par += 1
    n = len(rows)
    os.makedirs(carpeta, exist_ok=True)
    with open(os.path.join(carpeta, "manifiesto.jsonl"), "w", encoding="utf-8") as f:
        for j, r in enumerate(rows):
            r["id"] = j
            f.write(json.dumps({"idx": j, "id": j, "grupo": r["id_origen"], "etiqueta": int(r["tag"] == "compile_right_is_right")}) + "\n")
    y = np.array([1.0 if r["rol"] == "fiel" else (0.0 if r["rol"] == "infiel" else 0.5) for r in rows])
    for v, fuerza in (("completo", 0.8), ("solo_lean", 0.3), ("nl_desemparejado", 0.3), ("solo_nl", 0.0)):
        for pos in ("ultimo", "media_nl" if v == "solo_nl" else "media_lean"):
            X = rng.normal(size=(n, L, D)).astype(np.float32)
            X[:, :, 0] += fuerza * y[:, None]
            if v == "solo_nl":  # idéntico dentro del origen: el control 3 debe dar 0,5 exacto
                base = {r["id_origen"]: rng.normal(size=(L, D)).astype(np.float32) for r in rows}
                X = np.stack([base[r["id_origen"]] for r in rows])
            np.save(os.path.join(carpeta, f"acts_{v}_{pos}.npy"), X)
    py = rng.random((n, 8)).astype(np.float32)
    np.save(os.path.join(carpeta, "pyes_completo.npy"), py)
    datos = os.path.join(carpeta, "datos")
    os.makedirs(datos, exist_ok=True)
    with open(os.path.join(datos, "pares_indice.jsonl"), "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps({k: v for k, v in r.items() if k not in ("nl", "lean")}, ensure_ascii=False) + "\n")
    pq.write_table(pa.table({"id": pa.array([r["id"] for r in rows], pa.int64()),
                             "refined_statement": [r["nl"] for r in rows],
                             "autoformalization": [r["lean"] for r in rows]}),
                   os.path.join(datos, "pares_nivel_b.parquet"))
    return os.path.join(datos, "pares_indice.jsonl"), k_par


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--carpeta", default=None)
    ap.add_argument("--jobs", type=int, default=2)
    a = ap.parse_args()
    carpeta = a.carpeta or tempfile.mkdtemp(prefix="nivel_b_sintetico_")
    indice, n_pares = fabricar(carpeta)
    print(f"datos sintéticos en {carpeta}: {n_pares} pares")
    sys.path.insert(0, AQUI)
    import analizar_pares
    sys.argv = ["analizar_pares.py", "--carpeta", carpeta, "--indice", indice, "--nombre", "sintetico",
                "--salida", os.path.join(carpeta, "resultados"), "--jobs", str(a.jobs), "--rapido", "--prueba",
                "--umbral_minimo", "10", "--umbral_pares", "20", "--umbral_origenes", "10"]
    analizar_pares.main()
    R = json.load(open(os.path.join(carpeta, "resultados", "nivel_b_sintetico_rapido.json"), encoding="utf-8"))
    assert R["agrupamiento_pliegues"] == "archivo fuente" and R["n_archivos"] < R["n_origenes"]
    assert abs(R["secundarios"]["solo_nl"][0] - 0.5) < 1e-9, "solo_nl debe ser 0,5 exacto por construcción"
    for k in ("central_bootstrap_por_archivo", "superficie_cruzada", "verdad_infiel_verdadera_hipotesis",
              "verdad_infiel_refutada_conclusion", "sin_C2", "pares_compuestos", "original_vs_fiel"):
        assert k in R["secundarios"], k
    assert R["secundarios"]["superficie_cruzada"].get("condicion_del_positivo") is True
    print("PRUEBA SINTÉTICA OK:", R["decision"])


if __name__ == "__main__":
    main()
