"""Extracción SIN la pregunta «Is this formalization faithful?» (11 nov 2026).

Para qué. La sonda del piloto lee un prompt que termina pidiéndole al modelo que juzgue. Aquí se
extraen las mismas activaciones con el mismo prompt menos la pregunta, para dos cosas:

  1. Comprobar el instrumento (no usa etiquetas): en un modelo causal los tokens de Lean van ANTES
     de la pregunta, así que la lectura «media_lean» no puede depender de ella. Este script lo mide:
     compara las activaciones nuevas con las guardadas, fila por fila y capa por capa.
  2. Tener el «último token» sin pregunta, que sí cambia, para el análisis que diga la regla
     (probes/sin_pregunta/regla_BORRADOR.md). Este script NO ajusta ninguna sonda ni lee etiquetas.

Cómo. No modifica probes/extraer.py: lo importa y cambia EN MEMORIA dos plantillas (quita la pregunta
y nada más; se comprueba con un assert). Modelo, revisión y tipos salen del meta.json de la extracción
original. Variantes: completo y solo_lean. Reanudable, como extraer.py.

Salida: probes/activaciones/sin_pregunta/<nombre>/  (nivel a)   o   .../nivel_b_<nombre>/  (nivel b)
        con «_pruebaN» al final si se usa --comprobar N o --limite N.

Uso (desde la raíz de Proyecto Godel):
  HF_HUB_OFFLINE=1 biblioteca/.venv/bin/python -I probes/sin_pregunta/extraer_sin_pregunta.py \
      --nombre qwen3_4b --comprobar 20            # ~1 min: 20 filas y la comparación
  ... --nivel a --nombre qwen3_4b --bitacora      # las 500 filas del Nivel A
  ... --nivel b --nombre qwen3_4b --bitacora      # las 1086 filas del Nivel B
  ... --nombre qwen3_4b --solo_comparar           # repite la comparación sin cargar el modelo
"""
import argparse
import json
import os
import sys

AQUI = os.path.dirname(os.path.abspath(__file__))
PROBES = os.path.dirname(AQUI)
sys.path.insert(0, PROBES)

SIN_COMPLETO = "Natural-language statement:\n{nl}\n\nLean 4 formalization:\n```lean\n{lean}\n```"
SIN_SOLO_LEAN = "Lean 4 formalization:\n```lean\n{lean}\n```"
VARIANTES = ("completo", "solo_lean")


def comparar(ref, nueva):
    """Compara las activaciones sin pregunta (nueva) con las originales (ref), mismas filas.

    Esperado por la atención causal: en «media_lean» coseno ~1 en todas las capas (diferencia solo
    numérica) y capa 0 idéntica; en «ultimo» sí deben diferir. No usa etiquetas."""
    import numpy as np

    lee = lambda d: [json.loads(l) for l in open(os.path.join(d, "manifiesto.jsonl"), encoding="utf-8")]
    man_r, man_n = lee(ref), lee(nueva)
    n = len(man_n)
    if [m["id"] for m in man_n] != [m["id"] for m in man_r[:n]]:
        sys.exit("Las filas de la salida nueva no son las primeras de la referencia: no comparo.")
    res = {"referencia": os.path.relpath(ref, PROBES), "nueva": os.path.relpath(nueva, PROBES), "filas": n}
    print(f"\nComparación con {res['referencia']} ({n} filas)")
    print(f"{'variante':<10} {'posición':<11} {'coseno mín':>11} {'coseno med':>11} {'dif. rel. med':>14} "
          f"{'capa 0 máx|dif|':>16}")
    for v in VARIANTES:
        k = f"n_tokens_lean_{v}"
        if all(k in m for m in man_n) and all(k in m for m in man_r[:n]):
            res[f"tokens_lean_iguales_{v}"] = int(sum(a[k] == b[k] for a, b in zip(man_n, man_r)))
        for pos in ("media_lean", "ultimo"):
            A = np.load(os.path.join(ref, f"acts_{v}_{pos}.npy"), mmap_mode="r")
            B = np.load(os.path.join(nueva, f"acts_{v}_{pos}.npy"), mmap_mode="r")
            cos, rel = [], []
            for c in range(A.shape[1]):
                a = np.asarray(A[:n, c, :], dtype=np.float64)
                b = np.asarray(B[:n, c, :], dtype=np.float64)
                na, nb = np.linalg.norm(a, axis=1), np.linalg.norm(b, axis=1)
                cos.append((a * b).sum(1) / np.maximum(na * nb, 1e-30))
                rel.append(np.linalg.norm(a - b, axis=1) / np.maximum(na, 1e-30))
            cos, rel = np.array(cos), np.array(rel)  # (capas, filas)
            capa0 = float(np.abs(np.asarray(A[:n, 0, :], dtype=np.float64)
                                 - np.asarray(B[:n, 0, :], dtype=np.float64)).max())
            r = {"coseno_min": float(cos.min()), "coseno_mediana": float(np.median(cos)),
                 "dif_relativa_mediana": float(np.median(rel)), "capa0_max_abs_dif": capa0,
                 "coseno_min_por_capa": [round(float(x), 6) for x in cos.min(1)]}
            res[f"{v}_{pos}"] = r
            print(f"{v:<10} {pos:<11} {r['coseno_min']:>11.6f} {r['coseno_mediana']:>11.6f} "
                  f"{r['dif_relativa_mediana']:>14.6f} {capa0:>16.6f}")
    for v in VARIANTES:
        if f"tokens_lean_iguales_{v}" in res:
            print(f"{v}: {res[f'tokens_lean_iguales_{v}']} de {n} filas con el mismo número de tokens de Lean")
    print("Esperado: media_lean con coseno ~1 y capa 0 ~0 (la pregunta va después del Lean); "
          "ultimo distinto (ahí sí cambia el prompt).")
    with open(os.path.join(nueva, "comprobacion_causal.json"), "w", encoding="utf-8") as fh:
        json.dump(res, fh, ensure_ascii=False, indent=2)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nivel", choices=["a", "b"], default="a")
    ap.add_argument("--nombre", required=True, help="carpeta de la extracción original: qwen3_4b, gemma3_4b, ...")
    ap.add_argument("--comprobar", type=int, default=None, metavar="N", help="solo las primeras N filas, y compara")
    ap.add_argument("--limite", type=int, default=None)
    ap.add_argument("--bitacora", action="store_true")
    ap.add_argument("--solo_comparar", action="store_true", help="no carga el modelo; compara lo ya extraído")
    a = ap.parse_args()

    pre = "nivel_b_" if a.nivel == "b" else ""
    ref = os.path.join(PROBES, "activaciones", pre + a.nombre)
    meta = json.load(open(os.path.join(ref, "meta.json"), encoding="utf-8"))
    n = a.comprobar or a.limite
    salida = os.path.join(PROBES, "activaciones", "sin_pregunta", pre + a.nombre + (f"_prueba{n}" if n else ""))
    if a.solo_comparar:
        comparar(ref, salida)
        return

    import extraer  # carga torch y transformers; el modelo lo carga extraer.main()

    # El cambio es SOLO quitar la pregunta: si extraer.py cambiara sus plantillas, esto falla aquí.
    assert extraer.PLANTILLA_COMPLETO == SIN_COMPLETO + "\n\n" + extraer.PREGUNTA
    assert extraer.PLANTILLA_SOLO_LEAN == SIN_SOLO_LEAN + "\n\n" + extraer.PREGUNTA
    extraer.PLANTILLA_COMPLETO = SIN_COMPLETO
    extraer.PLANTILLA_SOLO_LEAN = SIN_SOLO_LEAN
    if a.nivel == "b":
        extraer.DATOS = os.path.join(PROBES, "nivel_b", "datos", "pares_nivel_b.parquet")

    dt_acts = meta.get("dtype_activaciones")
    args = ["extraer.py", "--modelo", meta["modelo"], "--revision", meta["revision"], "--salida", salida,
            "--variantes", *VARIANTES, "--dtype", meta.get("dtype_modelo") or "bfloat16",
            "--dtype_acts", dt_acts if dt_acts in ("float16", "float32") else "float16"]
    if not meta.get("plantilla_chat", True):
        args.append("--sin_chat")
    if n:
        args += ["--limite", str(n)]
    if a.bitacora:
        args += ["--bitacora", "--cada", "200"]
    os.makedirs(os.path.dirname(salida), exist_ok=True)
    sys.argv = args
    extraer.main()

    ruta_meta = os.path.join(salida, "meta.json")
    m = json.load(open(ruta_meta, encoding="utf-8"))
    m["sin_pregunta"] = True
    m["extraccion_de_referencia"] = os.path.relpath(ref, PROBES)
    m["nota"] = ("Mismo prompt que la referencia menos la pregunta final. pyes_* no es interpretable aquí "
                 "(no se preguntó nada); se guarda solo porque extraer.py lo escribe.")
    with open(ruta_meta, "w", encoding="utf-8") as fh:
        json.dump(m, fh, ensure_ascii=False, indent=2)
    comparar(ref, salida)


if __name__ == "__main__":
    main()
