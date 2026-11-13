#!/usr/bin/env python3
"""verifica_voz.py VIEJO.tex NUEVO.tex

Compara dos versiones de un .tex y comprueba que la reescritura solo tocó la prosa.

Obligatorio (si algo difiere, sale con código 1):
  1. multiconjunto de números (con signo y decimales) fuera del resumen: idéntico;
  2. claves de \\cite, \\ref y \\label: idénticas;
  3. contenido de cada entorno matemático, tabla y figura: idéntico;
  4. cada número que salió del resumen aparece en el cuerpo.
Informativo: palabras y cifras del resumen, conteo de frases que delimitan la evidencia,
nombres protegidos (\\vr{...}, lecturas, niveles, familias) y giros prohibidos.
"""
import re
import sys
from collections import Counter

MENOS = "\u2212"  # el signo − tipográfico que usa el artículo


def lee(ruta):
    with open(ruta, encoding="utf-8") as f:
        t = f.read()
    # quita comentarios de LaTeX (un % no escapado hasta el fin de línea)
    return re.sub(r"(?<!\\)%.*", "", t)


def parte(t):
    """Devuelve (resumen, resto). El resto incluye preámbulo, título y cuerpo."""
    m = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", t, re.S)
    if not m:
        return "", t
    return m.group(1), t[: m.start()] + t[m.end():]


# Signo: + o − siempre; el guion ASCII solo si no viene pegado a una palabra (Qwen3-4B no es −4).
NUM = re.compile(r"(?:[+" + MENOS + r"]|(?<![\w\-" + MENOS + r"])-)?\d+(?:\.\d+)?")


def numeros(t):
    return Counter(NUM.findall(t))


def claves(t, orden):
    c = Counter()
    for m in re.finditer(r"\\" + orden + r"\*?(?:\[[^\]]*\])*\{([^}]*)\}", t):
        for k in m.group(1).split(","):
            c[k.strip()] += 1
    return c


def norm(s):
    return re.sub(r"\s+", " ", s).strip()


def entornos(t, nombre):
    pat = r"\\begin\{" + nombre + r"\*?\}.*?\\end\{" + nombre + r"\*?\}"
    return [norm(x) for x in re.findall(pat, t, re.S)]


def matematicas(t):
    """Matemática en línea ($...$) y en bloque, fuera de tablas y figuras (esas se comparan enteras)."""
    for e in ("table", "figure"):
        t = re.sub(r"\\begin\{" + e + r"\*?\}.*?\\end\{" + e + r"\*?\}", " ", t, flags=re.S)
    out = []
    for e in ("equation", "align", "gather", "multline", "displaymath", "math"):
        out += entornos(t, e)
    out += [norm(x) for x in re.findall(r"\\\[(.*?)\\\]", t, re.S)]
    out += [norm(x) for x in re.findall(r"(?<!\\)\$\$(.+?)(?<!\\)\$\$", t, re.S)]
    t2 = re.sub(r"(?<!\\)\$\$.+?(?<!\\)\$\$", " ", t, flags=re.S)
    out += [norm(x) for x in re.findall(r"(?<!\\)\$(.+?)(?<!\\)\$", t2, re.S)]
    return Counter(out)


def dif(a, b):
    """Diferencia de multiconjuntos: (sobra en viejo, sobra en nuevo)."""
    return dict(a - b), dict(b - a)


def palabras(t):
    t = re.sub(r"\\ic\{([^}]*)\}\{([^}]*)\}", r"[\1, \2]", t)
    t = re.sub(r"\\(?:emph|textbf|textit|vr)\{([^}]*)\}", r"\1", t)
    t = re.sub(r"\\[a-zA-Z]+\*?(?:\[[^\]]*\])?", " ", t)
    t = re.sub(r"[{}~$\\]", " ", t)
    return len([w for w in t.split() if re.search(r"\w", w)])


FRASES = [  # las que delimitan la evidencia: se cuenta cuántas veces aparece cada una
    "exploratory", "post hoc", "not a replication", "No level alone supports", "preliminary",
    "exploratori", "no es una réplica", "Ningún nivel sostiene por sí solo", "preliminares",
]
PROHIBIDO = [
    "crucial", "precisely", "exactly", "notably", "importantly", "worth noting", "audit",
    "the model knows", "precisamente", "exactamente", "cabe destacar", "vale la pena notar",
    "auditar", "auditor", "el modelo sabe", "\u2014", "---",
]
PROTEGIDOS = [r"\\vr\{[^}]*\}", r"\((?:i|ii)\)", r"(?:Level|Levels|Nivel|Niveles)~[ABC]", r"\bC[23]\b",
              r"(?:famil(?:y|ies|ia|ias)) [ABC]\b"]


def main(viejo, nuevo):
    tv, tn = lee(viejo), lee(nuevo)
    rv, cv = parte(tv)
    rn, cn = parte(tn)
    fallos = 0

    def chequeo(titulo, a, b):
        nonlocal fallos
        sv, sn = dif(a, b)
        ok = not sv and not sn
        print(f"[{'OK' if ok else 'DIFIERE'}] {titulo}  (viejo: {sum(a.values())}, nuevo: {sum(b.values())})")
        if not ok:
            fallos += 1
            for nombre, d in (("solo en el viejo", sv), ("solo en el nuevo", sn)):
                for k, v in d.items():
                    print(f"    {nombre}: {v} x {k if len(str(k)) < 200 else str(k)[:200] + ' [...]'}")

    print(f"VIEJO: {viejo}\nNUEVO: {nuevo}\n")
    print("== 1. Números fuera del resumen ==")
    chequeo("multiconjunto de números", numeros(cv), numeros(cn))

    print("\n== 2. Claves ==")
    for orden in ("cite[a-z]*", "ref", "label", "includegraphics"):
        chequeo("\\" + orden.replace("[a-z]*", "*"), claves(tv, orden), claves(tn, orden))

    print("\n== 3. Matemática, tablas y figuras ==")
    chequeo("matemática en línea y en bloque", matematicas(tv), matematicas(tn))
    for e in ("table", "figure"):
        a, b = entornos(tv, e), entornos(tn, e)
        chequeo(f"entornos {e}", Counter(a), Counter(b))
        if a != b and Counter(a) == Counter(b):
            print("    (mismo contenido, distinto orden)")

    print("\n== 4. Números que salieron del resumen ==")
    nv, nn = numeros(rv), numeros(rn)
    salieron, entraron = dif(nv, nn)
    cuerpo = numeros(cn)
    sin_signo = Counter()
    for k, v in cuerpo.items():
        sin_signo[k.lstrip("+")] += v
    for k in sorted(salieron, key=lambda s: s.lstrip("+" + MENOS + "-")):
        if cuerpo[k]:
            print(f"    {k:>8}  en el cuerpo ({cuerpo[k]} veces)")
        elif sin_signo[k.lstrip('+')]:
            print(f"    {k:>8}  en el cuerpo como +{k.lstrip('+')} (extremo de intervalo con signo explícito en tabla)")
        else:
            print(f"    {k:>8}  NO ESTÁ EN EL CUERPO")
            fallos += 1
    if entraron:
        print("    [DIFIERE] números nuevos en el resumen:", entraron)
        fallos += 1
    print(f"    resumen viejo: {palabras(rv)} palabras, {sum(nv.values())} números; "
          f"nuevo: {palabras(rn)} palabras, {sum(nn.values())} números -> {sorted(nn.elements())}")

    print("\n== Informativo ==")
    for f in FRASES:  # se cuenta sin distinguir mayúsculas y con los saltos de línea normalizados
        a = [len(re.findall(re.escape(f), norm(x), re.I)) for x in (rv, cv)]
        b = [len(re.findall(re.escape(f), norm(x), re.I)) for x in (rn, cn)]
        if sum(a) or sum(b):
            print(f"    «{f}»: resumen {a[0]} -> {b[0]}, cuerpo {a[1]} -> {b[1]}"
                  f"{'' if a[1] == b[1] else '   <-- cambió en el cuerpo'}")
    for pat in PROTEGIDOS:
        a = Counter(re.findall(pat, cv))
        b = Counter(re.findall(pat, cn))
        sv, sn = dif(a, b)
        if sv or sn:
            print(f"    nombres protegidos {pat}: solo viejo {sv}, solo nuevo {sn}")
    prosa = tn
    for e in ("table", "figure"):
        prosa = re.sub(r"\\begin\{" + e + r"\*?\}.*?\\end\{" + e + r"\*?\}", " ", prosa, flags=re.S)
    hallados = {p: len(re.findall(re.escape(p), prosa, re.I)) for p in PROHIBIDO}
    hallados = {p: n for p, n in hallados.items() if n}
    print("    giros prohibidos en la prosa nueva:", hallados or "ninguno")

    print("\nRESULTADO:", "TODO IDÉNTICO" if not fallos else f"{fallos} DIFERENCIA(S)")
    return 1 if fallos else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
