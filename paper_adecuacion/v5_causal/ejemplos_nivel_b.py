#!/usr/bin/env python3
"""ejemplos_nivel_b.py — elige los pares de ejemplo de tab:bejemplos y escribe ejemplos_nivel_b.json (13 nov 2026).

Regla aprobada por Carlos el 13 de noviembre, antes de mirar los pares: dentro de cada familia (A, B, C2, C3), el
par con menos tokens editados y, en caso de empate, el primero por id. «Tokens editados» es la suma de
`tokens_editados` de los dos miembros; el id es el número de par en pares_indice_principal.jsonl (377 pares).

No corre ningún modelo. Lee el índice de pares y el parquet del Nivel B; nada se escribe a mano.
Uso (desde v5_causal):  ../../biblioteca/.venv/bin/python -I ejemplos_nivel_b.py
aplica_v5.py arma la tabla a partir del JSON y verifica_v5.py repite la selección contra el índice.
"""
import json
import os

AQUI = os.path.dirname(os.path.abspath(__file__))
DATOS = os.path.join(AQUI, "..", "..", "probes", "nivel_b", "datos")
FAMILIAS = ("A", "B", "C2", "C3")
# Único recorte de enunciado: en el par de C2 se muestra hasta aquí y se omiten las referencias que siguen.
CORTES = {"C2": r"\rceil$"}


def lee(nombre):
    return [json.loads(l) for l in open(os.path.join(DATOS, nombre), encoding="utf-8")]


def familia(infiel):
    if infiel["familia"] != "C":
        return infiel["familia"]
    return "C2" if infiel["regla"].startswith("C2") else "C3"


def seleccion():
    """{familia: (número de par, suma de tokens, nº de pares empatados, fiel, infiel)} según la regla."""
    pares = {}
    for r in lee("pares_indice_principal.jsonl"):
        if r["par"] is not None:
            pares.setdefault(r["par"], {})[r["rol"]] = r
    out = {}
    for k in sorted(pares):
        f, i = pares[k]["fiel"], pares[k]["infiel"]
        fam, suma = familia(i), f["tokens_editados"] + i["tokens_editados"]
        if fam not in out or suma < out[fam][1]:
            out[fam] = [k, suma, 1, f, i]
        elif suma == out[fam][1]:
            out[fam][2] += 1
    return out


def tex_lean(s):
    """Fragmento Lean literal en texttt. Los signos de comparación van en modo matemático: pdflatex no tiene ≤ ni ≥
    en esa fuente, y con babel en español `<` es un carácter activo que se come el espacio siguiente."""
    for u, m in (("≤", r"$\le$"), ("≥", r"$\ge$"), ("<", "$<$"), (">", "$>$")):
        s = s.replace(u, m)
    return r"\texttt{" + s + "}"


def tex_enunciado(e):
    """Enunciado literal del parquet, en una línea. `$$` pasa a `$` para que quepa en la celda."""
    t = " ".join((e["enunciado_hasta"] or e["enunciado"]).split()).replace("$$", "$")
    return t + (r" [\ldots]" if e["enunciado_hasta"] else "")


def celdas(e):
    """(original, fiel, infiel). Si la edición infiel toca otro fragmento que la fiel, cada celda lleva los dos."""
    f, i = e["fiel"], e["infiel"]
    if i["original"] == f["variante"]:
        return tex_lean(f["original"]), tex_lean(f["variante"]), tex_lean(i["variante"])
    nl = r" \newline "
    return (tex_lean(f["original"]) + nl + tex_lean(i["original"]), tex_lean(f["variante"]) + nl + tex_lean(i["original"]),
            tex_lean(f["variante"]) + nl + tex_lean(i["variante"]))


def filas_tex():
    out = []
    for e in json.load(open(os.path.join(AQUI, "ejemplos_nivel_b.json"), encoding="utf-8")):
        out.append(" & ".join((e["familia"], tex_enunciado(e)) + celdas(e)) + r"\\")
    return "\n\\addlinespace\n".join(out)


def main():
    import pyarrow.parquet as pq
    filas = {r["id"]: r for r in pq.read_table(os.path.join(DATOS, "pares_nivel_b.parquet")).to_pylist()}
    completo = {(r["id_candidato"], r["rol"], r.get("base_fiel")): r["id"] for r in lee("pares_indice.jsonl")}
    sel, out = seleccion(), []
    for fam in FAMILIAS:
        k, suma, empatados, f, i = sel[fam]
        pf = filas[completo[(f["id_candidato"], "fiel", f.get("base_fiel"))]]
        pi = filas[completo[(i["id_candidato"], "infiel", i.get("base_fiel"))]]
        assert pf["refined_statement"] == pi["refined_statement"], fam
        assert f["fragmento_variante"] in pf["autoformalization"], fam
        assert i["fragmento_variante"] in pi["autoformalization"], fam
        enunciado = pf["refined_statement"]
        hasta = None
        if fam in CORTES:
            hasta = enunciado[:enunciado.index(CORTES[fam]) + len(CORTES[fam])]
        out.append({"familia": fam, "par": k, "suma_tokens_editados": suma, "pares_empatados": empatados,
                    "id_origen": f["id_origen"], "enunciado": enunciado, "enunciado_hasta": hasta,
                    "fiel": {"original": f["fragmento_original"], "variante": f["fragmento_variante"]},
                    "infiel": {"original": i["fragmento_original"], "variante": i["fragmento_variante"]}})
        print(fam, "par", k, "suma", suma, "empatados", empatados)
    json.dump(out, open(os.path.join(AQUI, "ejemplos_nivel_b.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=1)


if __name__ == "__main__":
    main()
