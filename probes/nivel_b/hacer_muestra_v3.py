"""Tercera muestra (lote v3, 2026-11-04) -> muestra_30_v3.md. Igual que hacer_muestra_v2.py salvo las rutas; además muestra la dirección sintáctica de las C2.

Diferencias con hacer_muestra.py (que queda intacto, igual que muestra_30.md):
  - se toma de candidatos_v3.jsonl y SOLO entre candidatos que están en el emparejamiento provisional
    (lo que de verdad se analizaría);
  - estratificada por REGLA (infieles compuestas «X∘D» y fieles D), 1–3 por regla hasta ~30;
  - para cada caso se muestra el NL, el Lean ORIGINAL, la variante fiel D (base) y, si es una
    compuesta, la variante infiel, con la edición entre ⟦ ⟧;
  - se pregunta explícitamente si el ORIGINAL es fiel al NL (la premisa del diseño), además de si la
    etiqueta de la variante es correcta y la variante es sensata.

Uso: biblioteca/.venv/bin/python -I probes/nivel_b/hacer_muestra_v3.py
"""
import collections
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generar as G  # noqa: E402

N_OBJETIVO = 30


def marcar(texto, tramos, en_variante):
    s, pos = [], 0
    for a, b, r in sorted(tramos):
        s += [texto[pos:a], "⟦", r if en_variante else texto[a:b], "⟧"]
        pos = b
    s.append(texto[pos:])
    return "".join(s)


def recortar(marcado):
    return "\n".join(l for l in marcado.splitlines() if not l.startswith("import ")).strip()


def main():
    ruta = os.path.join(G.AQUI, "candidatos_v3.jsonl")
    cands = [json.loads(l) for l in open(ruta, encoding="utf-8")]
    idx = {c["id"]: c for c in cands}
    enpar = [c for c in cands if c["en_emparejamiento_provisional"]]
    por_regla = collections.defaultdict(list)
    for c in enpar:
        por_regla[c["regla"]].append(c)
    rng = random.Random(G.SEMILLA)
    reglas = sorted(por_regla, key=lambda r: (-len(por_regla[r]), r))
    cuota = {r: 1 for r in reglas}
    # las reglas más frecuentes reciben hasta 3 hasta llegar a ~30
    total = len(reglas)
    for r in reglas:
        while total < N_OBJETIVO and cuota[r] < 3 and cuota[r] < len(por_regla[r]):
            cuota[r] += 1; total += 1
        if total >= N_OBJETIVO:
            break
    elegidos = []
    for r in reglas:
        elegidos += rng.sample(por_regla[r], min(cuota[r], len(por_regla[r])))
    rng.shuffle(elegidos)
    resumen = json.load(open(os.path.join(G.AQUI, "resumen_generacion_v3.json"), encoding="utf-8"))
    L = ["# Muestra v3 (Nivel B) — para revisión de Carlos", "",
         f"Generada por `probes/nivel_b/hacer_muestra_v3.py` (semilla {G.SEMILLA}) sobre `candidatos_v3.jsonl` "
         f"({len(cands)} candidatos; SHA-256 `{resumen['sha256_candidatos']}`), **solo entre los {len(enpar)} candidatos "
         f"del emparejamiento provisional** ({resumen['emparejamiento_provisional']['pares']} pares), estratificada por regla "
         f"({len(reglas)} reglas; {len(elegidos)} casos). **Nada está certificado.** La edición va entre ⟦ ⟧. "
         "Se omiten las líneas `import`. `muestra_30.md` (v1) y `muestra_30_v2.md` quedan intactas como histórico. Lote v3: v2 + los 7 cambios de `revision_muestra_v2_fable.md` §4 (nombres de teorema neutros: `theorem T`).", "",
         "Para cada caso, tres preguntas: **(P0) ¿el Lean ORIGINAL es fiel al NL?** (premisa del diseño; si no, el par "
         "no vale); (P1) ¿la etiqueta esperada de la variante es correcta respecto al NL?; (P2) ¿la variante es un "
         "enunciado sensato (no un error de tipo disfrazado)? Anotar ✔/✘ y un comentario.", ""]
    for i, c in enumerate(elegidos, 1):
        nl = c["nl"].strip()
        if len(nl) > 700:
            nl = nl[:700] + " […]"
        comp = bool(c.get("base_fiel"))
        L += [f"## {i}. {c['regla']} ({c['familia_nombre']}) — etiqueta esperada: **{c['etiqueta_esperada']}**", "",
              f"- Origen: `{c['id_origen']}` (archivo `{c['archivo']}`; {c['fuente']}); zona: {c['zona']}; tokens editados "
              f"respecto al original (Qwen3-4B): {c['tokens_editados']}"
              + (f"; respecto a la base fiel: {c['tokens_editados_vs_base']}" if comp else "")
              + f"; dirección trivial: {c['direccion_trivial']}; correlato en el NL: {'sí' if c['correlato_nl'] else 'no'}", "",
              "**NL:**", "", "> " + nl.replace("\n", "\n> "), "",
              "**Lean original:**", "", "```lean", recortar(c["lean_original"]), "```", ""]
        tr = [tuple(t) for t in c["tramos"]]
        if comp:
            base = idx[c["base_fiel"]]
            trb = [tuple(t) for t in base["tramos"]]
            L += [f"**Variante fiel (base {base['regla']}, la otra mitad del par; edición respecto al original):**", "",
                  "```lean", recortar(marcar(base["lean_original"], trb, True)), "```", "",
                  f"**Variante infiel ({c['regla']}; edición respecto a la base):**", "",
                  "```lean", recortar(marcar(c["lean_base"], tr, True)), "```", ""]
        else:
            L += [f"**Variante ({c['regla']}; edición respecto al original):**", "",
                  "```lean", recortar(marcar(c["lean_original"], tr, True)), "```", ""]
        L += ["Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:", ""]
    open(os.path.join(G.AQUI, "muestra_30_v3.md"), "w", encoding="utf-8").write("\n".join(L))
    print("muestra_30_v3.md:", len(elegidos), "casos;", dict(collections.Counter(c["regla"] for c in elegidos)))


if __name__ == "__main__":
    main()
