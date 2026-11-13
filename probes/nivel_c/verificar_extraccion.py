"""Verificación SIN modelo de la parte (i) de lanzar.sh (no usa GPU ni carga pesos).

Importa extraer_c.py (solo funciones), lee el parquet, calcula el desarreglo, construye los cuatro
prompts de cada fila con el tokenizador de Qwen3-4B (CPU, caché local) y comprueba:
  - que el parquet tiene las columnas del esquema y etiquetas 0/1;
  - que el desarreglo es una permutación sin puntos fijos ni donantes del mismo grupo;
  - que cada prompt tiene bloque promediado no vacío y ningún prompt supera --max_tokens (4096);
  - que «Yes»/«No» y « Yes»/« No» son un solo token.
Además: misma plantilla que CriticLeanBench (comprueba que extraer_c reproduce el prompt de
extraer.py en 3 filas de CriticLeanBench) y estima el tiempo de la extracción.

Uso: biblioteca/.venv/bin/python -I probes/nivel_c/verificar_extraccion.py \
         --datos probes/nivel_c/datos_proc/proofnetverif.parquet
"""

import argparse
import collections
import importlib.util
import json
import os
import statistics

os.environ.setdefault("HF_HUB_OFFLINE", "1")

import numpy as np
import pyarrow.parquet as pq

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(os.path.dirname(AQUI))


def cargar_modulo(nombre, ruta):
    spec = importlib.util.spec_from_file_location(nombre, ruta)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--datos", required=True)
    ap.add_argument("--modelo", default="Qwen/Qwen3-4B")
    ap.add_argument("--revision", default="1cfa9a7208912126459214e8b04321603b3df60c")
    ap.add_argument("--s_por_pase_ref", type=float, default=0.75,
                    help="s/pase medido en CriticLeanBench (Qwen3-4B, MPS, prompts ~230 tokens)")
    ap.add_argument("--tokens_ref", type=float, default=230.0)
    a = ap.parse_args()

    ec = cargar_modulo("extraer_c", os.path.join(AQUI, "extraer_c.py"))
    eo = cargar_modulo("extraer_orig", os.path.join(RAIZ, "probes", "extraer.py"))
    from transformers import AutoTokenizer
    tok = AutoTokenizer.from_pretrained(a.modelo, revision=a.revision)
    chat = tok.chat_template is not None
    si_no = ec.ids_si_no(tok)

    tabla = pq.read_table(a.datos)
    for c in ("id", "source", "refined_statement", "autoformalization", "tag"):
        assert c in tabla.column_names, c
    filas = tabla.to_pylist()
    N = len(filas)
    etiquetas = [int(f["tag"] == "compile_right_is_right") for f in filas]
    donante, banda = ec.desarreglo(filas)
    grupos = [ec.grupo_de(f["refined_statement"]) for f in filas]
    assert sorted(donante) == list(range(N)), "el desarreglo no es una permutación"
    assert all(donante[i] != i for i in range(N))
    assert all(grupos[donante[i]] != grupos[i] for i in range(N)), "donante del mismo grupo"
    assert ec.desarreglo(filas) == (donante, banda), "desarreglo no determinista"

    n_tok = collections.defaultdict(list)
    n_bloque = collections.defaultdict(list)
    for i, f in enumerate(filas):
        for v in ec.VARIANTES:
            prompt, (c0, c1) = ec.construir_prompt(tok, f, v, chat, filas[donante[i]]["refined_statement"])
            enc = tok(prompt, return_offsets_mapping=True, add_special_tokens=False)
            off = np.array(enc["offset_mapping"])
            m = (off[:, 0] >= c0) & (off[:, 1] <= c1) & (off[:, 1] > off[:, 0])
            assert m.sum() > 0, f"bloque vacío fila {i} {v}"
            n_tok[v].append(len(enc["input_ids"]))
            n_bloque[v].append(int(m.sum()))
    maxtok = max(max(x) for x in n_tok.values())
    assert maxtok <= 4096, "hay prompts que se truncarían"

    # extraer_c reproduce el prompt de extraer.py (CriticLeanBench, 3 filas)
    cl = pq.read_table(os.path.join(RAIZ, "probes", "datos", "criticleanbench_test.parquet")).to_pylist()
    for j in (0, 1, 300):
        for v in ec.VARIANTES:
            assert ec.construir_prompt(tok, cl[j], v, chat, cl[(j + 7) % 500]["refined_statement"]) == \
                eo.construir_prompt(tok, cl[j], v, chat, cl[(j + 7) % 500]["refined_statement"])

    media_tok = statistics.mean(statistics.mean(x) for x in n_tok.values())
    pases = 4 * N
    # Escalado lineal con la longitud (cota prudente: a esta longitud domina el costo fijo por pase)
    s_lineal = a.s_por_pase_ref * media_tok / a.tokens_ref
    res = {
        "datos": os.path.relpath(os.path.abspath(a.datos), RAIZ), "n_filas": N,
        "positivas": sum(etiquetas), "negativas": N - sum(etiquetas),
        "plantilla_chat": chat, "ids_si_no": si_no,
        "tokens_por_variante": {v: {"mediana": statistics.median(x), "media": round(statistics.mean(x), 1),
                                    "max": max(x)} for v, x in n_tok.items()},
        "tokens_bloque_promediado": {v: {"min": min(x), "mediana": statistics.median(x)} for v, x in n_bloque.items()},
        "desarreglo": {"permutacion": True, "puntos_fijos": 0, "mismo_grupo": 0,
                       "misma_etiqueta_que_donante": sum(etiquetas[i] == etiquetas[donante[i]] for i in range(N))},
        "prompt_identico_a_extraer_py_en_criticleanbench": True,
        "pases": pases,
        "estimado_horas": {"a_s_por_pase_ref": round(pases * a.s_por_pase_ref / 3600, 2),
                           "escalado_por_tokens": round(pases * s_lineal / 3600, 2),
                           "s_por_pase_ref": a.s_por_pase_ref, "media_tokens": round(media_tok, 1)},
    }
    print(json.dumps(res, ensure_ascii=False, indent=2))
    with open(os.path.join(AQUI, "verificacion_extraccion.json"), "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False, indent=2)


if __name__ == "__main__":
    main()
