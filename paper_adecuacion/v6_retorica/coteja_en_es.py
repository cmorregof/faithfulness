#!/usr/bin/env python3
"""coteja_en_es.py EN.tex ES.tex — compara, párrafo a párrafo, la secuencia de números, citas, referencias
y nombres protegidos de las dos versiones. Si las dos dicen lo mismo, las secuencias coinciden."""
import re, sys
MENOS = "\u2212"
NUM = re.compile(r"(?:[+" + MENOS + r"]|(?<![\w\-" + MENOS + r"])-)?\d+(?:\.\d+)?")
def bloques(ruta):
    t = open(ruta, encoding="utf-8").read()
    t = re.sub(r"(?<!\\)%.*", "", t)
    t = t[t.index("\\begin{abstract}"):]
    for e in ("table", "figure"):
        t = re.sub(r"\\begin\{" + e + r"\}.*?\\end\{" + e + r"\}", "\n\n", t, flags=re.S)
    out = []
    for b in re.split(r"\n\s*\n|\\item|\\paragraph|\\section", t):
        b = b.strip()
        if not b: continue
        firma = (NUM.findall(b), re.findall(r"\\(?:cite[tp]?|ref)\{([^}]*)\}", b), re.findall(r"\\vr\{[^}]*\}", b),
                 re.findall(r"\((?:i|ii|a|b)\)", b), re.findall(r"\bC[23]\b|Qwen3-\dB|OLMo-2|Gemma(?:-3)?|Llama(?:-3\.1)?|DeepSeek|Goedel|Kimina|bge-m3", b))
        out.append((firma, b))
    return out
en, es = bloques(sys.argv[1]), bloques(sys.argv[2])
print(f"bloques de prosa: EN {len(en)}, ES {len(es)}")
malos = 0
for i, (a, b) in enumerate(zip(en, es)):
    if a[0] != b[0]:
        malos += 1
        print(f"\n--- bloque {i} difiere ---\nEN: {a[1][:160]!r}\nES: {b[1][:160]!r}")
        for nombre, x, y in zip(("números", "citas/refs", "vr", "lecturas/condiciones", "modelos/familias"), a[0], b[0]):
            if x != y: print(f"   {nombre}: EN {x}\n   {' ' * len(nombre)}  ES {y}")
print("\nRESULTADO:", "las secuencias coinciden en todos los bloques" if not malos and len(en) == len(es) else f"{malos} bloque(s) con diferencias")
