"""Muestra aleatoria de 30 candidatos para la revisión de Carlos -> muestra_30.md.

Estratificada por familia de regla (A 8, B 7, C 7, D 8; semilla 20261104); dentro de cada
familia, muestreo uniforme sobre TODOS los candidatos de candidatos.jsonl (el lote que se
aprobaría), así que las reglas frecuentes (C2, D6, D3) salen más. La edición va entre ⟦ ⟧.

Uso: python3 -I probes/nivel_b/hacer_muestra.py
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generar as G  # noqa: E402

CUOTA = {"A": 8, "B": 7, "C": 7, "D": 8}


def marcar(original, tramos, en_variante):
    """Original con ⟦lo quitado⟧, o variante con ⟦lo puesto⟧ (los tramos son sobre el original)."""
    s, pos = [], 0
    for a, b, r in sorted(tramos):
        s += [original[pos:a], "⟦", r if en_variante else original[a:b], "⟧"]
        pos = b
    s.append(original[pos:])
    return "".join(s)


def recortar(lean, marcado):
    """Quita líneas `import` para que la muestra sea legible (no cambian nada)."""
    return "\n".join(l for l in marcado.splitlines() if not l.startswith("import ")).strip()


def main():
    cands = [json.loads(l) for l in open(os.path.join(G.AQUI, "candidatos.jsonl"), encoding="utf-8")]
    rng = random.Random(G.SEMILLA)
    elegidos = []
    for fam, k in CUOTA.items():
        pool = [c for c in cands if c["familia"] == fam]
        elegidos += rng.sample(pool, k)
    rng.shuffle(elegidos)
    L = ["# Muestra aleatoria de 30 candidatos (Nivel B) — para revisión de Carlos", "",
         f"Generada por `probes/nivel_b/hacer_muestra.py` (semilla {G.SEMILLA}) sobre "
         f"`candidatos.jsonl` ({len(cands)} candidatos; SHA-256 en `resumen_generacion.json`). "
         "Estratificada por familia: A (más fuerte) 8, B (más débil) 7, C (otro teorema) 7, "
         "D (reescritura fiel) 8; uniforme dentro de cada familia. **Nada está certificado.** "
         "La edición va entre ⟦ ⟧ (en el original, lo que se quita o cambia; en la variante, lo "
         "que se pone). Se omiten las líneas `import`.", "",
         "Para cada caso: ¿la etiqueta esperada es correcta respecto al NL? ¿la variante es un "
         "enunciado sensato (no un error de tipo disfrazado)? Anotar ✔/✘ y un comentario.", ""]
    for i, c in enumerate(elegidos, 1):
        nl = c["nl"].strip()
        if len(nl) > 700:
            nl = nl[:700] + " […]"
        tr = [tuple(t) for t in c["tramos"]]
        L += [f"## {i}. {c['regla']} ({c['familia_nombre']}) — etiqueta esperada: **{c['etiqueta_esperada']}**", "",
              f"- Origen: `{c['id_origen']}` ({c['fuente']}); zona: {c['zona']}; tokens editados (Qwen3-4B): "
              f"{c['tokens_editados']}; dirección trivial: {c['direccion_trivial']}; "
              f"correlato en el NL: {'sí' if c['correlato_nl'] else 'no'}; en el emparejamiento provisional: "
              f"{'sí' if c['en_emparejamiento_provisional'] else 'no'}", "",
              "**NL:**", "", "> " + nl.replace("\n", "\n> "), "",
              "**Lean original:**", "", "```lean", recortar(c["lean_original"], marcar(c["lean_original"], tr, False)), "```", "",
              "**Variante:**", "", "```lean", recortar(c["lean_variante"], marcar(c["lean_original"], tr, True)), "```", "",
              "Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:", ""]
    open(os.path.join(G.AQUI, "muestra_30.md"), "w", encoding="utf-8").write("\n".join(L))
    print("muestra_30.md:", [c["id"] for c in elegidos])


if __name__ == "__main__":
    main()
