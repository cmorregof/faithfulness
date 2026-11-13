"""Convierte ProofNetVerif (PAug/ProofNetVerif@91183e5b) al esquema de probes/extraer.py.

Entrada (descargada el 4 nov 2026, datos no confiables: solo se leen como tablas):
  probes/nivel_c/datos/proofnetverif/data/{valid,test}-00000-of-00001.parquet
Salida:
  probes/nivel_c/datos_proc/proofnetverif.parquet
      id (int64, 0..N-1, orden: valid y luego test, orden original dentro de cada split)
      source              "ProofNetVerif/<split>/<libro>"   (libro = parte del id antes de «|»)
      refined_statement   nl_statement
      autoformalization   lean4_src_header + lean4_prediction  (mismo estilo que CriticLeanBench,
                          cuyo campo incluye «import Mathlib» y los «open»)
      tag                 "compile_right_is_right" si correct, "compile_unknown_is_false" si no
                          (ProofNetVerif no trae información de compilación)
      compila             null en todas las filas
      id_proofnet, split, lean4_formalization_ref   (columnas extra; extraer_c.py no las usa)
  probes/nivel_c/datos_proc/proofnetverif_manifiesto.jsonl
      idx, id, id_proofnet, split, source, etiqueta, grupo, compila (null), grupo_tipo, n_grupo
  probes/nivel_c/datos_proc/proofnetverif_resumen.json  (conteos y SHA-256)

Uso: biblioteca/.venv/bin/python -I probes/nivel_c/preparar_proofnetverif.py
"""

import collections
import hashlib
import json
import os
import unicodedata

import pyarrow as pa
import pyarrow.parquet as pq

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(os.path.dirname(AQUI))
ENTRADA = os.path.join(AQUI, "datos", "proofnetverif", "data")
SALIDA = os.path.join(AQUI, "datos_proc")
CRITICLEAN = os.path.join(RAIZ, "probes", "datos", "criticleanbench_test.parquet")
SHA_ESPERADO = {
    "valid-00000-of-00001.parquet": "d376127a467d92bcf7b42e1410b489695692d76f7af40f04d41042769751b86c",
    "test-00000-of-00001.parquet": "30287a8af51fc7bea2bec4fbfab6ae82ef5cf0de9f4c49b25f6ecfba4e7bb4a0",
}


def sha256(ruta):
    h = hashlib.sha256()
    with open(ruta, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def grupo_de(nl):
    """Igual que extraer.py: enunciado NL normalizado (NFKC, minúsculas, espacios)."""
    t = unicodedata.normalize("NFKC", nl).lower()
    t = " ".join(t.split())
    return hashlib.sha256(t.encode()).hexdigest()[:12]


def main():
    os.makedirs(SALIDA, exist_ok=True)
    filas = []
    for split in ("valid", "test"):
        nombre = f"{split}-00000-of-00001.parquet"
        ruta = os.path.join(ENTRADA, nombre)
        h = sha256(ruta)
        if h != SHA_ESPERADO[nombre]:
            raise SystemExit(f"SHA-256 distinto en {nombre}: {h}")
        for r in pq.read_table(ruta).to_pylist():
            filas.append((split, r))

    out = collections.defaultdict(list)
    man = []
    for i, (split, r) in enumerate(filas):
        cabecera = r["lean4_src_header"].rstrip() + "\n\n"
        lean = cabecera + r["lean4_prediction"].strip()
        tag = "compile_right_is_right" if r["correct"] else "compile_unknown_is_false"
        out["id"].append(i)
        out["source"].append(f"ProofNetVerif/{split}/{r['id'].split('|')[0]}")
        out["refined_statement"].append(r["nl_statement"])
        out["autoformalization"].append(lean)
        out["tag"].append(tag)
        out["compila"].append(None)
        out["id_proofnet"].append(r["id"])
        out["split"].append(split)
        out["lean4_formalization_ref"].append(r["lean4_formalization"])
        man.append({"idx": i, "id": i, "id_proofnet": r["id"], "split": split,
                    "source": out["source"][-1], "etiqueta": int(bool(r["correct"])),
                    "grupo": grupo_de(r["nl_statement"]), "compila": None})

    # Tipo de grupo: solo positivas, solo negativas o mixto (el bootstrap estratifica por esto)
    por_grupo = collections.defaultdict(list)
    for m in man:
        por_grupo[m["grupo"]].append(m["etiqueta"])
    for m in man:
        e = set(por_grupo[m["grupo"]])
        m["grupo_tipo"] = "mixto" if len(e) == 2 else ("pos" if e == {1} else "neg")
        m["n_grupo"] = len(por_grupo[m["grupo"]])

    esquema = pa.schema([("id", pa.int64()), ("source", pa.string()),
                         ("refined_statement", pa.string()), ("autoformalization", pa.string()),
                         ("tag", pa.string()), ("compila", pa.int64()),
                         ("id_proofnet", pa.string()), ("split", pa.string()),
                         ("lean4_formalization_ref", pa.string())])
    ruta_pq = os.path.join(SALIDA, "proofnetverif.parquet")
    pq.write_table(pa.table(dict(out), schema=esquema), ruta_pq)
    ruta_man = os.path.join(SALIDA, "proofnetverif_manifiesto.jsonl")
    with open(ruta_man, "w", encoding="utf-8") as f:
        for m in man:
            f.write(json.dumps(m, ensure_ascii=False) + "\n")

    # Comprobaciones y resumen
    grupos_id = collections.defaultdict(set)
    for m in man:
        grupos_id[m["id_proofnet"]].add(m["grupo"])
    tipos = collections.Counter()
    for g, e in por_grupo.items():
        tipos["mixto" if len(set(e)) == 2 else ("pos" if set(e) == {1} else "neg")] += 1
    cl = pq.read_table(CRITICLEAN).to_pylist()
    solape = {grupo_de(r["refined_statement"]) for r in cl} & set(por_grupo)
    res = {
        "fuente": "https://huggingface.co/datasets/PAug/ProofNetVerif",
        "revision": "91183e5b12d64374827bf2782db629b5b0f8f319",
        "licencia": "MIT (ficha de Hugging Face)",
        "sha256_entrada": SHA_ESPERADO,
        "n_filas": len(man),
        "n_por_split": dict(collections.Counter(m["split"] for m in man)),
        "n_positivas": sum(m["etiqueta"] for m in man),
        "n_grupos": len(por_grupo),
        "grupos_por_tipo": dict(tipos),
        "filas_en_grupos_mixtos": sum(m["grupo_tipo"] == "mixto" for m in man),
        "ids_proofnet_con_mas_de_un_grupo": sum(len(v) > 1 for v in grupos_id.values()),
        "grupos_por_id_proofnet_iguales": len(grupos_id) == len(por_grupo),
        "solape_de_grupos_con_criticleanbench": len(solape),
        "compila": "null en todas las filas: ProofNetVerif no trae información de compilación",
        "sha256_salida": {"proofnetverif.parquet": sha256(ruta_pq),
                          "proofnetverif_manifiesto.jsonl": sha256(ruta_man)},
    }
    with open(os.path.join(SALIDA, "proofnetverif_resumen.json"), "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False, indent=2)
    print(json.dumps(res, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
