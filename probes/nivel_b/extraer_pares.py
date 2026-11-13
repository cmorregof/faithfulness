"""Adaptador del Nivel B para probes/extraer.py (que NO se modifica). PREPARADO; NO LANZADO CON MODELO.

1. Toma los candidatos CERTIFICADOS (certificar.py): fieles con estado «equivalente» e infieles con
   estado «no_equivalente»: nivel 2 si la edición está en una hipótesis (testigo que cumple las
   demás hipótesis: descarta hipótesis redundantes) y nivel ≥ 1 si está en la conclusión. Rehace el emparejamiento por tamaño de
   edición SOLO con ellos (generar.emparejar: mismo intervalo de tokens editados, misma clase de
   objeto, misma zona; semilla fija).
2. Escribe un parquet con el esquema que espera extraer.py (id int64, source, refined_statement,
   autoformalization, tag) con, por cada origen con al menos un par: el original (tag
   compile_right_is_right), y por cada par la variante infiel (compile_right_is_false) y la fiel
   (compile_right_is_right). El NL es el mismo en todas las filas de un origen, así que el «grupo»
   de extraer.py (hash del NL) agrupa por origen. Y un índice pares_indice.jsonl (id -> rol, par,
   regla, tokens, nivel, verdad de la variante…).
3. Salvo con --solo_parquet: importa probes/extraer.py, cambia su constante DATOS al parquet nuevo
   y llama a su main() con las mismas variantes y posiciones (completo, solo_lean, solo_nl,
   nl_desemparejado; «ultimo» y «media_lean»/«media_nl»). Reanudable como extraer.py.

Uso (lo llama lanzar.sh; no correr a mano sin las aprobaciones):
  biblioteca/.venv/bin/python -I probes/nivel_b/extraer_pares.py --solo_parquet
  biblioteca/.venv/bin/python -I probes/nivel_b/extraer_pares.py --salida probes/activaciones/nivel_b_qwen3_4b --bitacora
Prueba sin certificación (SOLO para probar la tubería; nunca para el análisis):
  ... --sin_certificar --solo_parquet --dir_parquet <carpeta temporal>
"""
import argparse
import collections
import json
import os
import sys

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import generar as G  # noqa: E402

TAG_SI, TAG_NO = "compile_right_is_right", "compile_right_is_false"


def certificados(cands, ruta_res, nivel_hip=2, nivel_concl=1, sin_certificar=False):
    if sin_certificar:
        return [dict(c, estado_cert="(sin certificar)", nivel=None) for c in cands]
    res = {}
    for l in open(ruta_res, encoding="utf-8"):
        r = json.loads(l)
        res[r["id"]] = r
    out = []
    for c in cands:
        r = res.get(c["id"])
        if not r:
            continue
        if c["familia"] == "D" and r["estado"] == "equivalente":
            out.append(dict(c, estado_cert=r["estado"], nivel=None, verdad_variante="igual a la del original"))
        elif c["familia"] != "D" and r["estado"] == "no_equivalente" and \
                (r.get("nivel") or 0) >= (nivel_hip if c["zona"] == "hipotesis" else nivel_concl):
            out.append(dict(c, estado_cert=r["estado"], nivel=r.get("nivel"),
                            verdad_variante=r.get("verdad_variante"),
                            direccion_probada=r.get("direccion_probada")))
    return out


def filas(cert):
    idx = {c["id"]: c for c in cert}
    pares = G.emparejar(cert)
    por_origen = collections.defaultdict(list)
    for k, (i, f) in enumerate(pares):
        por_origen[idx[i]["id_origen"]].append((k, i, f))
    out = []
    for o in sorted(por_origen):
        c0 = idx[por_origen[o][0][1]]
        archivo = c0.get("archivo") or G.archivo_de(o)  # v2: pliegues agrupados por archivo fuente
        out.append(dict(rol="original", id_candidato=None, id_origen=o, archivo=archivo, par=None, nl=c0["nl"],
                        lean=c0["lean_original"], tag=TAG_SI, fuente=c0["fuente"], regla="original",
                        familia="O"))
        for k, i, f in por_origen[o]:
            for rol, cid, tag in (("infiel", i, TAG_NO), ("fiel", f, TAG_SI)):
                c = idx[cid]
                out.append(dict(rol=rol, id_candidato=cid, id_origen=o, archivo=archivo, par=k, nl=c["nl"],
                                lean=c["lean_variante"], tag=tag, fuente=c["fuente"], regla=c["regla"],
                                familia=c["familia"], zona=c["zona"], objeto=c["objeto"],
                                tokens_editados=c["tokens_editados"], bin_edicion=c["bin_edicion"],
                                tokens_editados_vs_base=c.get("tokens_editados_vs_base"),
                                base_fiel=c.get("base_fiel"), version=c.get("version", 1),
                                fragmento_original=c["fragmento_original"],
                                fragmento_variante=c["fragmento_variante"],
                                nivel=c.get("nivel"), verdad_variante=c.get("verdad_variante")))
    for j, r in enumerate(out):
        r["id"] = j
        r["grupo"] = G.grupo_de(r["nl"].strip())
    return out, pares


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidatos", default=os.path.join(AQUI, "candidatos.jsonl"))
    ap.add_argument("--resultados", default=os.path.join(AQUI, "certificacion", "resultados.jsonl"))
    ap.add_argument("--nivel_hipotesis", type=int, default=2)
    ap.add_argument("--nivel_conclusion", type=int, default=1)
    ap.add_argument("--dir_parquet", default=os.path.join(AQUI, "datos"))
    ap.add_argument("--solo_parquet", action="store_true")
    ap.add_argument("--sin_certificar", action="store_true", help="SOLO pruebas de la tubería")
    a, resto = ap.parse_known_args()

    import pyarrow as pa
    import pyarrow.parquet as pq

    cands = [json.loads(l) for l in open(a.candidatos, encoding="utf-8")]
    cert = certificados(cands, a.resultados, a.nivel_hipotesis, a.nivel_conclusion, a.sin_certificar)
    rows, pares = filas(cert)
    os.makedirs(a.dir_parquet, exist_ok=True)
    ruta_pq = os.path.join(a.dir_parquet, "pares_nivel_b.parquet")
    tabla = pa.table({
        "id": pa.array([r["id"] for r in rows], pa.int64()),
        "source": [f"nivelB|{r['fuente']}|{r['rol']}|{r['regla']}" for r in rows],
        "refined_statement": [r["nl"] for r in rows],
        "autoformalization": [r["lean"] for r in rows],
        "tag": [r["tag"] for r in rows],
    })
    pq.write_table(tabla, ruta_pq)
    with open(os.path.join(a.dir_parquet, "pares_indice.jsonl"), "w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps({k: v for k, v in r.items() if k not in ("nl", "lean")}, ensure_ascii=False) + "\n")
    cuenta = collections.Counter(r["rol"] for r in rows)
    fam = collections.Counter(r["familia"] for r in rows if r["rol"] == "infiel")
    print(json.dumps(dict(parquet=os.path.relpath(ruta_pq, G.RAIZ), filas=len(rows), por_rol=dict(cuenta),
                          pares=len(pares), origenes=cuenta["original"], infieles_por_familia=dict(fam),
                          certificados=len(cert), sin_certificar=a.sin_certificar), ensure_ascii=False))
    if a.solo_parquet:
        return
    if a.sin_certificar:
        sys.exit("--sin_certificar es solo para probar la tubería; no se extrae con modelo.")
    sys.path.insert(0, os.path.join(G.RAIZ, "probes"))
    import extraer  # noqa: E402  (carga torch/transformers; el modelo lo carga su main())
    extraer.DATOS = ruta_pq
    sys.argv = ["extraer.py"] + resto
    extraer.main()


if __name__ == "__main__":
    main()
