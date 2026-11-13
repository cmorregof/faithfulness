"""Generador de candidatos del Nivel B (pares mínimos NL ↔ Lean 4). NO certifica nada.

Lee (solo lectura):
  prometeo_lean/aprobados/Corpus/corpus_v2.jsonl   filas de formal_conjectures con docstring al final
                                                    de `contexto_lean` (se toma el ÚLTIMO `/--`)
  datos/FormalMATH-Lite/FormalMATH_lite.json        refined_statement + autoformalization
Escribe (en probes/nivel_b/):
  candidatos.jsonl            un candidato por línea (todas las reglas, sin certificar)
  resumen_generacion.json     aplicabilidad por regla, conteos, tamaños de edición, emparejamiento
                              provisional (antes de certificar)

Las reglas están definidas en reglas_generador.md (mismos nombres). Cada regla devuelve ediciones
como tramos (inicio, fin, reemplazo) sobre la cadena Lean original, así la variante conserva el
formato y la edición es mínima. Determinista: semilla fija, orden fijo de fuentes y de sitios.

Tamaño de edición: tokens de Qwen3-4B (solo el tokenizador; HF_HUB_OFFLINE=1) cambiados entre
el Lean original y la variante: suma, sobre los bloques no iguales de difflib.SequenceMatcher
(autojunk=False) de las dos listas de ids, de max(tokens quitados, tokens puestos).

Uso:
  HF_HUB_OFFLINE=1 biblioteca/.venv/bin/python -I probes/nivel_b/generar.py          (lote v1, histórico)
  HF_HUB_OFFLINE=1 biblioteca/.venv/bin/python -I probes/nivel_b/generar.py --v2     (lote v2: candidatos_v2.jsonl)
  (--sin_tokenizador: cuenta tokens con una expresión regular; solo para pruebas)

v2 (revisor Fable, 2026-11-04): filtros de NL, correlato de orden para las reglas de relación y pares
(X∘D, D) con la misma reescritura fiel en ambos miembros; ver el bloque «Versión 2» más abajo y
reglas_generador.md. Los candidatos compuestos llevan `lean_base` (la variante D), `base_fiel` (id de
la D), tramos relativos a `lean_base` y `tokens_editados_vs_base`.
"""

import argparse
import collections
import difflib
import hashlib
import json
import os
import random
import re
import statistics
import sys
import unicodedata

RAIZ = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
AQUI = os.path.join(RAIZ, "probes", "nivel_b")
CORPUS = os.path.join(RAIZ, "prometeo_lean", "aprobados", "Corpus", "corpus_v2.jsonl")
FORMALMATH = os.path.join(RAIZ, "datos", "FormalMATH-Lite", "FormalMATH_lite.json")
MODELO_TOK = "Qwen/Qwen3-4B"
REVISION_TOK = "1cfa9a7208912126459214e8b04321603b3df60c"
SEMILLA = 20261104
DEPS_OK = {"Mathlib", "FormalConjecturesForMathlib"}  # lo que corpus_lean tiene compilado
NL_MIN, NL_MAX, LEAN_MAX = 30, 3000, 2500

FAMILIA = {"A": "mas_fuerte", "B": "mas_debil", "C": "otro_teorema", "D": "reescritura_fiel"}
# Intervalos de tamaño de edición (tokens) para emparejar infiel con fiel dentro del mismo origen.
BINS = [(1, 4), (5, 8), (9, 14), (15, 24), (25, 10**9)]
MAX_PARES_POR_ORIGEN = 2
# Reglas fieles que dejan una huella superficial alineada con la etiqueta (medido sobre todos los
# candidatos: D3 y D6 añaden un subíndice o una prima en el 100 % de los casos; D2 y D7 añaden «¬»
# en el 98–100 %). Se generan y certifican, pero NO entran en los pares del análisis principal:
# un lector que solo ve el Lean podría separar «fiel» por la huella.
EXCLUIR_DE_PARES = {"D2", "D3", "D6", "D7"}

# ---- Versión 2 del lote (revisor Fable, 2026-11-04; se activa con --v2; escribe candidatos_v2.jsonl).
# Motivo: sobre los 730 pares provisionales de v1, unigramas y bigramas del Lean variante SOLO
# separaban fiel de infiel con AUROC pareada ≈ 0,85 (D1 introduce >/≥; D8 produce «1 ≤ x», «0 < x»;
# B3 produce «2 < x», «3 < x»): la identidad de la regla era legible en el Lean. En v2:
#   (a) NL ≥ 60 caracteres, sin restos de Lean (LEANISH) y sin notas que no son enunciados (NOTA);
#   (b) A2/A3/B2/B3/C3 exigen un correlato DE ORDEN en el NL (ORDEN_NL), no solo una letra;
#   (c) las reglas de relación/numeral entran en los pares solo COMPUESTAS con una reescritura fiel:
#       par = (D∘X, D) con D ∈ COMPONER_D y X ∈ COMPONER_X, ambos miembros con la misma firma de D y
#       distintos solo en X. Las X puras se generan y certifican, pero no entran en los pares;
#   (d) D1/D1c/D8 puras solo emparejan con sus compuestas; A1/B1/B4/C1 emparejan por intervalo con
#       D4h/D4c/D5 (reglas sin huella medida de operador o numeral);
#   (e) cada candidato lleva `archivo` (archivo fuente de formal_conjectures o la fila de FormalMATH)
#       para agrupar pliegues por archivo, no solo por enunciado.
V2 = False
NL_MIN_V2 = 60
LEANISH = re.compile(r"-/|/-|\babbrev\b|\binstance\b|:=|\bnamespace\b|^\s*def\b|^\s*theorem\b|^\s*lemma\b", re.M)
NOTA = re.compile(r"^\s*(\**\s*)?(the case\b|value of the sequence|see \[|a weak form|the lower-bound half|"
                  r"proved by|this (problem|is|follows|was)\b|\*?reference:?\*?\s*\[|cf\.|compare )", re.I)
ORDEN_NL = re.compile(r"at most|at least|less than|greater than|more than|smaller|larger|exceed|positive|"
                      r"negative|strictly|nonneg|non-neg|bounded|\\le|\\ge|\\lt|\\gt|\\neq|[<>≤≥⩾⩽≠]|"
                      r"\bmax|\bmin|\bupper\b|\blower\b|\bbound", re.I)
# Bases fieles con las que se compone cada edición infiel. D1/D1c/D8 no mueven binders (los índices
# de certificar.piezas siguen valiendo); D4h solo se usa con A1 (piezas localiza la hipótesis quitada
# por su texto) y D4c solo con B4 (zona conclusión). X no tiene que ser aplicable al original: basta
# que lo sea a la variante D (así `2 ≤ k` da B3∘D1 = `k > 2` y también A3∘D8 = `1 ≤ k`, y la
# estrictez del operador deja de predecir la etiqueta).
COMPONER = {"A2": ("D1", "D1c", "D8"), "A3": ("D1", "D1c", "D8"), "B2": ("D1", "D1c", "D8"),
            "B3": ("D1", "D1c", "D8"), "C2": ("D1", "D1c", "D8"), "C3": ("D1", "D1c", "D8"),
            "A1": ("D4h", "D1", "D8"), "B1": ("D1", "D8", "D4h"), "B4": ("D4c",)}
COMPONER_D = ("D1", "D1c", "D8", "D4h", "D4c")
COMPONER_X = tuple(COMPONER)
# v2: en los pares solo entran compuestas (infiel) con su propia base (fiel); las puras se generan
# y certifican, pero no emparejan.
EXCLUIR_DE_PARES_V2 = EXCLUIR_DE_PARES | set(COMPONER_X) | {"C1"}
SOLO_CON_COMPUESTAS = set(COMPONER_D) | {"D5"}

# ---- Versión 3 del lote (revisiones Opus + Fable de muestra_30_v2, 2026-11-04; --v3 implica las
# reglas de v2 y escribe candidatos_v3.jsonl). Cambios (numeración de revision_muestra_v2_fable.md §4):
#   1. B1 no se compone (B1∘D fuera de los pares; B1 pura se genera pero ya no emparejaba);
#   3. si D1 cae a la conclusión, coincide con D1c: se descarta la D1 (y sus compuestas); además
#      se descarta cualquier candidato cuyo Lean variante repite otro del mismo origen;
#   4. enunciados Lean idénticos (sin el nombre) en orígenes distintos: se conserva el primero;
#   5. orígenes con el original no fiel vistos en las revisiones (EXCLUIR_ORIGENES_V3);
#   6. nombre de teorema neutro (`theorem T`) en original, base y variante;
#   7. las C2 cuyo numeral es un lado entero de una comparación de orden llevan la dirección
#      sintáctica (como A3/B3 en hipótesis, A2/B2 en conclusión) en `direccion_trivial`.
#   (2: la comprobación de vacuidad del original está en certificar.py.)
V3 = False
NOMBRE_NEUTRO = "T"
EXCLUIR_ORIGENES_V3 = {
    "FormalMATH_lite[69]",   # caso 24 de muestra_30_v2: hipótesis inconsistente (f 0 = 1 y f 0 = −1)
    "FormalMATH_lite[97]",   # Fable: 100 * b = 200 y 60 * 2 * b = 300, original vacuo
    "formal_conjectures:ErdosProblems/1190:Erdos1190.erdos_1190.variants.lt_one",  # caso 25: no usa eps (sSup)
    # revision_cambios_v3_*: A3 deja `0 ≤ D` dentro de `∃ D : ℤ`; con D = 0 la variante es trivialmente
    # demostrable (x ∣ 0) y se ve sin leer el NL. El filtro de ediciones vacuas no mira dentro de ∃.
    "formal_conjectures:OEIS/211417:OeisA211417.general_divisibility",
    # revision_filtro_v3_opus: la conclusión del Lean original es `True`; no es fiel al NL y la
    # comprobación de vacuidad (solo hipótesis) no lo ve.
    "FormalMATH_lite[286]",
}


def neutralizar_nombre(lean):
    """`theorem Erdos.foo …` -> `theorem T …` (solo el primer theorem/lemma)."""
    return re.sub(r"\b(theorem|lemma)(\s+)[^\s(\[{⦃:]+", lambda m: m.group(1) + m.group(2) + NOMBRE_NEUTRO,
                  lean, count=1)


def direccion_c2(frag_o, N, zona, pos=None):
    """v3: dirección sintáctica de N -> N+1 cuando el numeral EDITADO (posición `pos` en frag_o) es un
    lado entero de una comparación de orden. Devuelve (direccion_trivial, familia_sintactica) o None.
    Arreglo (revisiones Opus/Fable de muestra_30_v3): antes se miraba qué lado era igual a N, no qué
    aparición se editó (Falconer_two: `2 * dimH E > 2`, se edita el 2 de la izquierda)."""
    c = comparacion_pura(frag_o)
    rel = ops_relacion(frag_o, REL_ORDEN)
    if not c or pos is None or len(rel) != 1:
        return None
    lhs, op, rhs = c
    pos_op = rel[0][0]
    izq = lhs.strip() == str(N) and pos < pos_op
    der = rhs.strip() == str(N) and pos > pos_op
    if izq == der:
        return None
    # ¿el predicado editado se vuelve más fuerte (menos valores lo cumplen)?
    mas_fuerte = (izq and op in ("≤", "<")) or (der and op in ("≥", ">"))
    if zona == "hipotesis":  # hipótesis más fuerte -> teorema más débil
        return ("original ⇒ variante", "B") if mas_fuerte else ("variante ⇒ original", "A")
    return ("variante ⇒ original", "A") if mas_fuerte else ("original ⇒ variante", "B")


def archivo_de(id_origen):
    """Archivo fuente: «OEIS/24356» en formal_conjectures; la propia fila en FormalMATH-Lite."""
    m = re.match(r"formal_conjectures:([^:]+):", id_origen)
    return m.group(1) if m else id_origen


def nl_es_enunciado(nl):
    """Filtros de NL de v2: longitud, sin restos de Lean, no es una nota."""
    return len(nl) >= NL_MIN_V2 and not LEANISH.search(nl) and not NOTA.search(nl)


def edicion_trivial_en_nat(frag_v, p):
    """v2: la edición deja una comparación entre el numeral 0 y una variable de tipo ℕ que es vacua
    (`0 ≤ n`, `n ≥ 0`) o imposible (`n < 0`, `0 > n`). Se ve sin leer el NL (y A3 en `0 < n` es
    el caso más frecuente del lote); por eso no entra en v2."""
    m = re.fullmatch(r"\s*(?:0\s*(≤|>)\s*(" + IDENT + r")|(" + IDENT + r")\s*(≥|<)\s*0)\s*", frag_v or "")
    if not m:
        return False
    v = m.group(2) or m.group(3)
    return tipos_datos(p).get(v, "").strip() in ("ℕ", "Nat")

SIGNADOS = ("ℝ", "ℚ", "ℤ", "Real", "Rat", "Int", "ℂ", "Complex")
# Funciones/proyecciones de Mathlib o FormalConjecturesForMathlib de valor ℕ, ℝ≥0∞ o no negativas por
# construcción (vistas en el lote v3; el tipo no está en el contexto del archivo).
NO_NEGATIVAS = {"minDegree", "maxDegree", "totient", "volume", "upperDensity", "lowerDensity", "density",
                "secondSmallestDegree", "distEven", "card", "ncard", "encard", "girth", "egirth",
                "chromaticNumber", "cliqueNum", "natAbs", "length"}


def _codominio(tipo):
    """`ℕ → ℝ` -> `ℝ`; `Fin 5 → ℝ` -> `ℝ`; `ℕ` -> `ℕ`."""
    return re.split(r"→", tipo)[-1].strip() if tipo else ""


def tipo_en_contexto(nombre, ctx):
    """Tipo de resultado de `nombre` según el contexto del archivo: `def nombre … : T :=` o un binder
    de `variable` `(… nombre … : T)`. None si no se encuentra."""
    if not ctx:
        return None
    m = re.search(r"\b(?:def|abbrev)\s+(?:[\w.]*\.)?" + re.escape(nombre) + r"\b[^\n]*?:\s*([^:=\n]+?)\s*:=", ctx)
    if m:
        return m.group(1)
    m = re.search(r"\bvariable\b[^\n]*[({]\s*(?:[\w']+\s+)*" + re.escape(nombre) + r"(?:\s+[\w']+)*\s*:\s*([^)}]+)[)}]", ctx)
    return m.group(1) if m else None


def edicion_vacua(frag_v, p, ctx=""):
    """v3 (arreglo de las revisiones de muestra_30_v3, afinado tras revision_cambios_v3_*): la edición
    deja `0 ≤ t`, `t ≥ 0`, `t < 0` o `0 > t` con `t` un término simple cuyo valor NO puede ser negativo
    según su tipo, que se busca para la cabeza del término (`a` en `a n`, `minDegree` en `G.minDegree`):
      1. variable o función declarada en los binders: se mira el codominio (`a : ℕ → ℝ` -> ℝ: se conserva);
      2. si no, `def`/`variable` del contexto del archivo;
      3. si no, la lista NO_NEGATIVAS (Mathlib/FC);
      4. tipo desconocido: se CONSERVA (antes se descartaba; así salían Serre y FM[286]/FM[416]).
    Cualquier variable declarada ℝ/ℚ/ℤ dentro del término también lo conserva (`t - 5`, `b^2 - 4*a*c`).
    En ℕ la comparación es vacua o imposible y se ve sin leer el NL; los `ε ≥ 0` reales se conservan."""
    m = re.fullmatch(r"\s*(?:0\s*(?:≤|>)\s*(.+?)|(.+?)\s*(?:≥|<)\s*0)\s*", frag_v or "", re.S)
    if not m:
        return False
    t = (m.group(1) or m.group(2)).strip()
    if re.search(r"[≤≥<>=≠∧∨→↔∀∃,¬]", t):
        return False
    td = tipos_datos(p)
    if any(_codominio(td.get(x, "")) in SIGNADOS for x in ident_en(t)):
        return False
    cab = re.match(r"\(?\s*(" + IDENT + r"(?:\." + IDENT + r")*)", t)
    if not cab:
        return False
    partes = cab.group(1).split(".")
    # proyección `x.f` o `(N k).totient`: manda el último campo
    proy = re.search(r"\.(" + IDENT + r")\s*$", t)
    nombre = proy.group(1) if proy else partes[-1]
    if not proy and partes[0] in td:
        return _codominio(td[partes[0]]) not in SIGNADOS
    tc = tipo_en_contexto(nombre, ctx)
    if tc is not None:
        return _codominio(tc) not in SIGNADOS
    return nombre in NO_NEGATIVAS


def edicion_descartable(frag_v, p, ctx=""):
    return edicion_vacua(frag_v, p, ctx) if V3 else edicion_trivial_en_nat(frag_v, p)


# ---------------------------------------------------------------- utilidades de texto

ABRE, CIERRA = "([{⦃⟨", ")]}⦄⟩"
REL_ORDEN = ("≤", "≥", "<", ">")
NUMERICOS = {"ℕ", "ℤ", "ℚ", "ℝ", "Nat", "Int", "Rat", "Real"}
# símbolos que rompen la monotonía o el alcance simple de una relación
NO_MONOTONO = re.compile(r"[¬→↔{}|λ↦]|\bfun\b|\bif\b|\blet\b|=>|\bhave\b|\bshow\b|\bmatch\b")
NOTACION_LIGADORA = re.compile(r"[∑∏∫⋃⋂⨆⨅∀∃,]|\bfun\b|λ|↦")
IDENT = r"[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'₀-₉²³!?]*"


def grupo_de(nl):
    """Igual que probes/extraer.py: hash del NL normalizado (agrupa todas las variantes de un origen)."""
    t = unicodedata.normalize("NFKC", nl).lower()
    t = " ".join(t.split())
    return hashlib.sha256(t.encode()).hexdigest()[:12]


def profundidades(s):
    """Profundidad de paréntesis (de cualquier tipo) antes de cada carácter."""
    d, out = 0, []
    for ch in s:
        if ch in CIERRA:
            d -= 1
        out.append(d)
        if ch in ABRE:
            d += 1
    return out


def ops_relacion(s, ops=REL_ORDEN + ("≠", "="), solo_nivel0=False):
    """Posiciones de operadores de relación rodeados de espacios: [(pos, op)]."""
    prof = profundidades(s)
    res = []
    for m in re.finditer(r"(?<= )(≤|≥|<|>|≠|=)(?= )", s):
        if m.group(1) not in ops:
            continue
        if solo_nivel0 and prof[m.start()] != 0:
            continue
        res.append((m.start(), m.group(1)))
    return res


def termino_puro(t):
    t = t.strip()
    return bool(t) and not NOTACION_LIGADORA.search(t) and not NO_MONOTONO.search(t) \
        and not ops_relacion(" " + t + " ") and not re.search(r"[∧∨]", t)


def ident_en(texto):
    return set(re.findall(IDENT, texto))


def tokens_nl(nl):
    return set(re.findall(r"[A-Za-z]+|\d+", nl))


def correlato(fragmento, nl, excluir=()):
    """¿Algún identificador corto (≤ 3 caracteres, que no sea nombre de hipótesis) o numeral del
    fragmento editado aparece como palabra en el NL? Filtro débil, declarado en las reglas."""
    tn = tokens_nl(nl)
    for x in re.findall(r"\d+|" + IDENT, fragmento):
        if x in excluir or (x[:1] in "hH" and len(x) > 1 and not x.isdigit()):
            continue
        base = re.sub(r"[₀-₉'₀-₉]+$", "", x)
        if (x.isdigit() or 1 <= len(base) <= 3) and (base in tn or x in tn):
            return True
    return False


# ---------------------------------------------------------------- análisis sintáctico

def analizar(lean):
    """theorem nombre binders : conclusión := by [sorry]  →  dict con posiciones absolutas."""
    m = re.search(r"\b(theorem|lemma)\s+([^\s(\[{⦃:]+)", lean)
    if not m:
        return None
    fin = re.search(r":=\s*(?:by\s*)?(?:sorry\s*)?$", lean)
    if not fin:
        return None
    i, n = m.end(), len(lean)
    binders, depth, start = [], 0, None
    while i < n:
        ch = lean[i]
        if depth == 0:
            if ch in "({[⦃":
                depth, start = 1, i
            elif ch == ":" and lean[i:i + 2] != ":=":
                break
            elif not ch.isspace():
                return None
        else:
            if ch in ABRE:
                depth += 1
            elif ch in CIERRA:
                depth -= 1
                if depth == 0:
                    binders.append((start, i + 1))
        i += 1
    else:
        return None
    c0, c1 = i + 1, fin.start()
    if c1 <= c0:
        return None
    bs = []
    for a, b in binders:
        txt = lean[a:b]
        inner = txt[1:-1]
        prof = profundidades(inner)
        k = next((j for j, ch in enumerate(inner) if ch == ":" and prof[j] == 0
                  and inner[j:j + 2] != ":="), None)
        if k is None:
            nombres, tipo, t0 = [], inner.strip(), a + 1
        else:
            nombres, tipo = inner[:k].split(), inner[k + 1:]
            t0 = a + 1 + k + 1
        lead = len(tipo) - len(tipo.lstrip())
        tipo_s = tipo.strip()
        es_hip = txt[0] == "(" and bool(nombres) and all(x[:1] in "hH" for x in nombres)
        bs.append(dict(txt=txt, ini=a, fin=b, clase=txt[0], nombres=nombres, tipo=tipo_s,
                       tipo_ini=t0 + lead, tipo_fin=t0 + lead + len(tipo_s), hip=es_hip))
    concl_raw = lean[c0:c1]
    lead = len(concl_raw) - len(concl_raw.lstrip())
    concl = concl_raw.strip()
    return dict(pre=lean[:m.start()], nombre=m.group(2), binders=bs, concl=concl,
                c_ini=c0 + lead, c_fin=c0 + lead + len(concl), cola=lean[c1:])


def aplicar(lean, tramos):
    out, pos = [], 0
    for a, b, r in sorted(tramos):
        if a < pos:
            raise ValueError("tramos solapados")
        out.append(lean[pos:a]); out.append(r); pos = b
    out.append(lean[pos:])
    return "".join(out)


def tipos_datos(p):
    """nombre -> tipo de los binders de datos (no hipótesis)."""
    t = {}
    for b in p["binders"]:
        if not b["hip"]:
            for x in b["nombres"]:
                t[x] = b["tipo"]
    return t


def relacion_simple(s):
    """Fórmula con exactamente una relación de orden, en contexto monótono. Devuelve (pos, op)."""
    if NO_MONOTONO.search(s) or "·" in s:
        return None
    rel = ops_relacion(s, REL_ORDEN)
    if len(rel) != 1:
        return None
    pos, op = rel[0]
    if profundidades(s)[pos] != 0:  # dentro de un argumento: monotonía desconocida
        return None
    # restricción de un ligador («∀ n ≥ 1,», «∃ x > 0,»): posición antítona o de alcance; se excluye
    if re.search(r"[∀∃]\s*(?:" + IDENT + r"\s*)+$", s[:pos]):
        return None
    return rel[0]


def comparacion_pura(s, ops=REL_ORDEN):
    """s == «lhs op rhs» con lhs y rhs términos puros. Devuelve (lhs, op, rhs)."""
    rel = ops_relacion(s, ops + tuple(o for o in REL_ORDEN + ("≠", "=") if o not in ops))
    if len(rel) != 1 or rel[0][1] not in ops:
        return None
    pos, op = rel[0]
    lhs, rhs = s[:pos].strip(), s[pos + len(op):].strip()
    if not (termino_puro(lhs) and termino_puro(rhs)):
        return None
    return lhs, op, rhs


def numerico(fragmento, p):
    """Evidencia de orden lineal: todas las variables del enunciado que aparecen son de tipo
    numérico y hay al menos una variable numérica o un numeral."""
    td = tipos_datos(p)
    ids = ident_en(fragmento)
    usadas = [x for x in ids if x in td]
    if any(td[x].strip() not in NUMERICOS for x in usadas):
        return False
    return bool(usadas) or bool(re.search(r"\d", fragmento)) or ": ℝ)" in fragmento


# ---------------------------------------------------------------- reglas
# Cada regla: f(lean, p, nl) -> lista de dicts {tramos, zona, binder, frag_o, frag_v}
# Se toma el PRIMER sitio aplicable (orden: hipótesis de izquierda a derecha, luego conclusión).

def _sitio(tramos, zona, binder, frag_o, frag_v, **extra):
    return dict(tramos=tramos, zona=zona, binder=binder, frag_o=frag_o, frag_v=frag_v, **extra)


def _cambiar_op(s, s0, cambio):
    r = relacion_simple(s)
    if not r or r[1] not in cambio:
        return None
    pos, op = r
    return (s0 + pos, s0 + pos + len(op), cambio[op]), s[:pos] + cambio[op] + s[pos + len(op):]


def R_A1(lean, p, nl):
    """Quitar una hipótesis (relación) cuyo nombre no se use en otra parte."""
    if len(p["binders"]) < 3:
        return []
    for k, b in enumerate(p["binders"]):
        if not b["hip"] or len(b["nombres"]) != 1:
            continue
        if not comparacion_pura(b["tipo"], REL_ORDEN + ("≠",)):  # solo hipótesis atómicas
            continue
        resto = lean[:b["ini"]] + lean[b["fin"]:]
        if re.search(r"(?<![\w.'])" + re.escape(b["nombres"][0]) + r"(?![\w'])", resto):
            continue
        if not correlato(b["tipo"], nl):
            continue
        a = b["ini"]
        while a > 0 and lean[a - 1] in " \t":
            a -= 1
        e = b["fin"]
        if a > 0 and lean[a - 1] == "\n":  # binder solo en su línea: quitar la línea
            a -= 1
        return [_sitio([(a, e, "")], "hipotesis", k, b["txt"], "")]
    return []


def _correlato_orden(nl):
    """v2: las reglas de relación exigen que el NL hable de orden (no basta una letra)."""
    return (not V2) or bool(ORDEN_NL.search(nl))


def _hip_op(cambio, lean, p, nl, regla):
    if not _correlato_orden(nl):
        return []
    for k, b in enumerate(p["binders"]):
        if not b["hip"] or len(b["nombres"]) != 1:
            continue
        r = _cambiar_op(b["tipo"], b["tipo_ini"], cambio)
        if r and correlato(b["tipo"], nl):
            tramo, frag_v = r
            return [_sitio([tramo], "hipotesis", k, b["tipo"], frag_v)]
    return []


def _concl_op(cambio, lean, p, nl):
    if not _correlato_orden(nl):
        return []
    r = _cambiar_op(p["concl"], p["c_ini"], cambio)
    if r and correlato(p["concl"], nl):
        tramo, frag_v = r
        return [_sitio([tramo], "conclusion", None, p["concl"], frag_v)]
    return []


def R_A2(lean, p, nl):
    return _concl_op({"≤": "<", "≥": ">"}, lean, p, nl)


def R_A3(lean, p, nl):
    return _hip_op({"<": "≤", ">": "≥"}, lean, p, nl, "A3")


def R_B2(lean, p, nl):
    return _concl_op({"<": "≤", ">": "≥"}, lean, p, nl)


def R_B3(lean, p, nl):
    return _hip_op({"≤": "<", "≥": ">"}, lean, p, nl, "B3")


def R_C3(lean, p, nl):
    return _concl_op({"≤": "≥", "≥": "≤", "<": ">", ">": "<"}, lean, p, nl)


PALABRAS_SIGNO = re.compile(r"positive|nonnegative|non-negative|natural|negative|nonzero|non-zero|"
                            r"\\gt|\\geq?|\\lt|\\leq?|[<>≤≥]|\\neq|≠", re.I)


def R_B1(lean, p, nl):
    """Añadir (h_<v>_pos : 0 < v) a una variable real/entera/racional que el NL no restringe."""
    if PALABRAS_SIGNO.search(nl):
        return []
    td = tipos_datos(p)
    hips = " ".join(b["tipo"] for b in p["binders"] if b["hip"])
    for b in p["binders"]:
        if b["hip"] or b["clase"] != "(" or b["tipo"] not in ("ℝ", "ℤ", "ℚ"):
            continue
        for v in b["nombres"]:
            if re.search(r"(?<![\w.'])" + re.escape(v) + r"(?![\w'])", hips) and \
               re.search(r"(0|1)\s*[<≤]\s*" + re.escape(v) + r"\b|\b" + re.escape(v) + r"\s*[>≥≠]\s*0", hips):
                continue
            if v not in tokens_nl(nl):
                continue
            nombre = f"h{v}_pos"
            if nombre in lean:
                continue
            ultimo = p["binders"][-1]
            nuevo = f" ({nombre} : 0 < {v})"
            return [_sitio([(ultimo["fin"], ultimo["fin"], nuevo)], "hipotesis", len(p["binders"]),
                           "", nuevo.strip(), variable=v, tipo_variable=td.get(v))]
    return []


def _conjuncion_nivel0(s):
    """s = A ∧ B con un único ∧ de nivel 0 y nada que cambie el alcance antes de él."""
    if NO_MONOTONO.search(s) or re.search(r"[∀∃∑∏∫⋃⋂⨆⨅∨]", s):
        return None
    prof = profundidades(s)
    pos = [i for i, ch in enumerate(s) if ch == "∧" and prof[i] == 0]
    if len(pos) != 1:
        return None
    a, b = s[:pos[0]].rstrip(), s[pos[0] + 1:].lstrip()
    if not a or not b or "," in s:
        return None
    return a, b


def R_B4(lean, p, nl):
    r = _conjuncion_nivel0(p["concl"])
    if not r:
        return []
    a, b = r
    if not correlato(b, nl):
        return []
    return [_sitio([(p["c_ini"], p["c_fin"], a)], "conclusion", None, p["concl"], a)]


def R_C1(lean, p, nl):
    m = re.match(r"∀\s+(\w+)\s*(:\s*[^,]+)?,\s*∃\s+(\w+)\s*(:\s*[^,]+)?,\s*(.*)$", p["concl"], re.S)
    if not m:
        return []
    x, tx, y, ty, cuerpo = m.groups()
    if tx and re.search(r"\b%s\b" % re.escape(y), tx) or ty and re.search(r"\b%s\b" % re.escape(x), ty):
        return []
    if not re.search(r"(?<![\w.'])%s(?![\w'])" % re.escape(x), cuerpo):
        return []
    nuevo = "∃ %s%s, ∀ %s%s, %s" % (y, (" " + ty.strip()) if ty else "", x,
                                    (" " + tx.strip()) if tx else "", cuerpo)
    return [_sitio([(p["c_ini"], p["c_fin"], nuevo)], "conclusion", None, p["concl"], nuevo)]


NUMERAL = re.compile(r"(?<![\w.₀-₉])(\d+)(?![\w.₀-₉])")


def R_C2(lean, p, nl):
    """N -> N+1 en un numeral (N ≥ 2) que aparece en el NL; antes en hipótesis que en conclusión."""
    tn = tokens_nl(nl)
    zonas = [(b["tipo"], b["tipo_ini"], "hipotesis", k) for k, b in enumerate(p["binders"]) if b["hip"]]
    zonas.append((p["concl"], p["c_ini"], "conclusion", None))
    for s, s0, zona, k in zonas:
        for m in NUMERAL.finditer(s):
            N = int(m.group(1))
            if N < 2 or m.group(1) not in tn:
                continue
            antes = s[:m.start()].rstrip()
            if antes.endswith(("^", "Fin", "!")):
                continue
            tramo = (s0 + m.start(), s0 + m.end(), str(N + 1))
            return [_sitio([tramo], zona, k, s, s[:m.start()] + str(N + 1) + s[m.end():],
                           numeral=N, **({"pos_numeral": m.start()} if V3 else {}))]
    return []


def _espejo(s, s0, zona, k, lean, p):
    c = comparacion_pura(s)
    if not c:
        return None
    lhs, op, rhs = c
    nuevo = f"{rhs} {dict(zip('≤≥<>', '≥≤><'))[op]} {lhs}"
    return _sitio([(s0, s0 + len(s), nuevo)], zona, k, s, nuevo)


def R_D1(lean, p, nl):
    """Espejo: a < b -> b > a (hipótesis primero; si no, conclusión)."""
    for k, b in enumerate(p["binders"]):
        if b["hip"] and len(b["nombres"]) == 1:
            r = _espejo(b["tipo"], b["tipo_ini"], "hipotesis", k, lean, p)
            if r:
                return [r]
    r = _espejo(p["concl"], p["c_ini"], "conclusion", None, lean, p)
    return [r] if r else []


def R_D1c(lean, p, nl):
    """D1 solo en la conclusión (para emparejar con A2/B2/C3)."""
    r = _espejo(p["concl"], p["c_ini"], "conclusion", None, lean, p)
    return [r] if r else []


def _ne(s, s0, zona, k):
    c = comparacion_pura(s, ("≠",))
    if c:
        lhs, _, rhs = c
        nuevo = f"¬({lhs} = {rhs})"
        return _sitio([(s0, s0 + len(s), nuevo)], zona, k, s, nuevo)
    m = re.fullmatch(r"¬\s*\((.*)\)", s.strip(), re.S) or re.fullmatch(r"¬\s*(.*)", s.strip(), re.S)
    if m:
        c = comparacion_pura(m.group(1).strip(), ("=",))
        if c:
            nuevo = f"{c[0]} ≠ {c[2]}"
            return _sitio([(s0, s0 + len(s), nuevo)], zona, k, s, nuevo)
    return None


def R_D2(lean, p, nl):
    for k, b in enumerate(p["binders"]):
        if b["hip"] and len(b["nombres"]) == 1:
            r = _ne(b["tipo"], b["tipo_ini"], "hipotesis", k)
            if r:
                return [r]
    r = _ne(p["concl"], p["c_ini"], "conclusion", None)
    return [r] if r else []


PATRON_NOMBRE = r"(?<![\w.'₀-₉])%s(?![\w'₀-₉])"


def _renombrar(texto, v, nv):
    return re.sub(PATRON_NOMBRE % re.escape(v), nv, texto)


def _tramos_renombre(texto, desde, v, nv):
    """Un tramo por aparición (así la edición marcada es solo el nombre)."""
    return [(desde + m.start(), desde + m.end(), nv) for m in re.finditer(PATRON_NOMBRE % re.escape(v), texto)]


def R_D3(lean, p, nl, contexto=""):
    """Renombrar una variable ligada (∀/∃) de la conclusión: v -> v₁ en todo el enunciado."""
    c = p["concl"]
    td = tipos_datos(p)
    for m in re.finditer(r"[∀∃]\s+(" + IDENT + r")", c):
        v = m.group(1)
        if v in td or v[:1] in "hH" or len(v) > 3:
            continue
        nv = v + "₁"
        if nv in lean or nv in contexto:
            continue
        nc = _renombrar(c, v, nv)
        if nc == c or nc.count(nv) < 2:
            continue
        return [_sitio(_tramos_renombre(c, p["c_ini"], v, nv), "conclusion", None, c, nc, variable=v)]
    return []


def R_D4h(lean, p, nl):
    """Intercambiar dos hipótesis adyacentes independientes."""
    bs = p["binders"]
    for k in range(len(bs) - 1):
        b1, b2 = bs[k], bs[k + 1]
        if not (b1["hip"] and b2["hip"]):
            continue
        if any(re.search(r"(?<![\w.'])%s(?![\w'])" % re.escape(x), b2["txt"]) for x in b1["nombres"]):
            continue
        sep = lean[b1["fin"]:b2["ini"]]
        nuevo = b2["txt"] + sep + b1["txt"]
        return [_sitio([(b1["ini"], b2["fin"], nuevo)], "hipotesis", k,
                       lean[b1["ini"]:b2["fin"]], nuevo)]
    return []


def R_D4c(lean, p, nl):
    """Conmutar el único ∧ de nivel 0 de la conclusión (A ∧ B -> B ∧ A)."""
    r = _conjuncion_nivel0(p["concl"])
    if not r:
        return []
    a, b = r
    nuevo = f"{b} ∧ {a}"
    return [_sitio([(p["c_ini"], p["c_fin"], nuevo)], "conclusion", None, p["concl"], nuevo)]


def R_D5(lean, p, nl):
    """x ∈ Set.Icc a b -> a ≤ x ∧ x ≤ b (pertenencia suelta), o ∀ x ∈ Icc a b, P -> ∀ x, a ≤ x ∧ x ≤ b → P."""
    s, s0 = p["concl"], p["c_ini"]
    pat = r"(?:Set\.|Finset\.)?Icc\s+(" + IDENT + r"|\d+)\s+(" + IDENT + r"|\d+)"
    m = re.search(r"∀\s+(" + IDENT + r")\s*∈\s*" + pat + r"\s*,", s)
    if m:
        x, a, b = m.groups()
        nuevo = f"∀ {x}, {a} ≤ {x} ∧ {x} ≤ {b} →"
        return [_sitio([(s0 + m.start(), s0 + m.end(), nuevo)], "conclusion", None, m.group(0), nuevo)]
    for k, bd in enumerate(p["binders"]):
        if bd["hip"]:
            m = re.fullmatch(r"(" + IDENT + r")\s*∈\s*" + pat, bd["tipo"])
            if m:
                x, a, b = m.groups()
                nuevo = f"{a} ≤ {x} ∧ {x} ≤ {b}"
                return [_sitio([(bd["tipo_ini"], bd["tipo_fin"], nuevo)], "hipotesis", k, bd["tipo"], nuevo)]
    return []


def R_D6(lean, p, nl):
    """Renombrar una hipótesis: h -> h₀ (o h' si ya termina en subíndice) en todo el enunciado."""
    for k, b in enumerate(p["binders"]):
        if not b["hip"] or len(b["nombres"]) != 1:
            continue
        v = b["nombres"][0]
        nv = v + ("'" if re.search(r"[₀-₉\d']$", v) else "₀")
        if re.search(r"(?<![\w.'])%s(?![\w'])" % re.escape(nv), lean):
            continue
        a, e = b["ini"], p["c_fin"]
        return [_sitio(_tramos_renombre(lean[a:e], a, v, nv), "hipotesis", k, b["txt"],
                       b["txt"].replace(v, nv, 1), variable=v)]
    return []


def _neg_opuesta(s, s0, zona, k, p):
    c = comparacion_pura(s)
    if not c or not numerico(s, p):
        return None
    lhs, op, rhs = c
    if op == "≤":
        nuevo = f"¬({rhs} < {lhs})"
    elif op == "<":
        nuevo = f"¬({rhs} ≤ {lhs})"
    elif op == "≥":
        nuevo = f"¬({lhs} < {rhs})"
    else:
        nuevo = f"¬({lhs} ≤ {rhs})"
    return _sitio([(s0, s0 + len(s), nuevo)], zona, k, s, nuevo)


def R_D7(lean, p, nl):
    """a ≤ b -> ¬(b < a), a < b -> ¬(b ≤ a), en orden lineal (tipos numéricos)."""
    for k, b in enumerate(p["binders"]):
        if b["hip"] and len(b["nombres"]) == 1:
            r = _neg_opuesta(b["tipo"], b["tipo_ini"], "hipotesis", k, p)
            if r:
                return [r]
    r = _neg_opuesta(p["concl"], p["c_ini"], "conclusion", None, p)
    return [r] if r else []


DISCRETOS = {"ℕ", "ℤ", "Nat", "Int"}


def _desplazar(s, s0, zona, k, p):
    """En ℕ/ℤ: N ≤ x -> N-1 < x, N < x -> N+1 ≤ x, x ≤ N -> x < N+1, x < N -> x ≤ N-1 (y los
    simétricos con ≥, >). Solo si el otro lado es aritmética simple (+, *, -) de variables del
    enunciado de tipo ℕ/ℤ y numerales; nunca si el resultado sería un numeral negativo."""
    c = comparacion_pura(s)
    if not c:
        return None
    lhs, op, rhs = c
    if re.fullmatch(r"\d+", lhs):
        N, otro, izq = int(lhs), rhs, True
    elif re.fullmatch(r"\d+", rhs):
        N, otro, izq = int(rhs), lhs, False
    else:
        return None
    td = tipos_datos(p)
    if not re.fullmatch(r"[\w\s+*\-()\u2080-\u2089']+", otro):
        return None
    ids = [x for x in re.findall(IDENT, otro)]
    if not ids or any(td.get(x, "").strip() not in DISCRETOS for x in ids):
        return None
    # (op del numeral visto desde el numeral) -> (nuevo op, desplazamiento)
    tabla_izq = {"≤": ("<", -1), "<": ("≤", +1), "≥": (">", +1), ">": ("≥", -1)}
    tabla_der = {"≤": ("<", +1), "<": ("≤", -1), "≥": (">", -1), ">": ("≥", +1)}
    nop, d = (tabla_izq if izq else tabla_der)[op]
    if N + d < 0:
        return None
    nuevo = f"{N + d} {nop} {otro}" if izq else f"{otro} {nop} {N + d}"
    return _sitio([(s0, s0 + len(s), nuevo)], zona, k, s, nuevo, numeral=N)


def R_D8(lean, p, nl):
    """Desplazar la cota en dominios discretos (ℕ/ℤ): 2 ≤ n -> 1 < n."""
    for k, b in enumerate(p["binders"]):
        if b["hip"] and len(b["nombres"]) == 1:
            r = _desplazar(b["tipo"], b["tipo_ini"], "hipotesis", k, p)
            if r:
                return [r]
    r = _desplazar(p["concl"], p["c_ini"], "conclusion", None, p)
    return [r] if r else []


REGLAS = collections.OrderedDict([
    ("A1", R_A1), ("A2", R_A2), ("A3", R_A3),
    ("B1", R_B1), ("B2", R_B2), ("B3", R_B3), ("B4", R_B4),
    ("C1", R_C1), ("C2", R_C2), ("C3", R_C3),
    ("D1", R_D1), ("D1c", R_D1c), ("D2", R_D2), ("D3", R_D3), ("D4h", R_D4h), ("D4c", R_D4c),
    ("D5", R_D5), ("D6", R_D6), ("D7", R_D7), ("D8", R_D8),
])
# Qué se edita (para preferir pares infiel/fiel que editan la misma clase de objeto).
OBJETO = {"A1": {"hipotesis"}, "A2": {"relacion"}, "A3": {"relacion"}, "B1": {"hipotesis"},
          "B2": {"relacion"}, "B3": {"relacion"}, "B4": {"conjuncion"}, "C1": {"cuantificador"},
          "C2": {"numeral"}, "C3": {"relacion"}, "D1": {"relacion"}, "D1c": {"relacion"},
          "D2": {"relacion"}, "D3": {"nombre"}, "D4h": {"hipotesis"}, "D4c": {"conjuncion"},
          "D5": {"relacion"}, "D6": {"nombre"}, "D7": {"relacion"}, "D8": {"relacion", "numeral"}}
DIRECCION = {"A": "variante ⇒ original", "B": "original ⇒ variante", "C": "ninguna", "D": "ambas"}
DIRECCION_REGLA = {"C1": "variante ⇒ original"}


def objeto(regla):
    """Clase de objeto editado; para una compuesta «X∘D» (v2), la unión de las dos."""
    return set().union(*(OBJETO[r] for r in regla.split("∘")))


def familia(regla):
    return regla[0]


def etiqueta(regla):
    return "adecuada" if familia(regla) == "D" else "inadecuada"


# ---------------------------------------------------------------- fuentes

def doc_nl(contexto):
    c = contexto.rstrip()
    if not c.endswith("-/"):
        return None
    k = c.rfind("/--")
    if k < 0:
        return None
    cuerpo = c[k + 3:-2]
    # Revisor (Fable, 2026-11-04): si entre el último «/--» y el «-/» final hay otro cierre «-/», el
    # contexto termina en un comentario corriente «/- … -/» posterior al docstring, y el texto tomado
    # mezclaba el docstring con código Lean (ejemplo: WrittenOnTheWallII/Test.petersen_girth, caso 25
    # de muestra_30.md: el «NL» contenía `abbrev Star5 …` e `instance …`). Se descarta el origen.
    # Al regenerar cambian candidatos.jsonl y su SHA-256; hay que registrar el nuevo.
    if "-/" in cuerpo:
        return None
    return cuerpo.strip()


def cargar_origenes():
    origenes = []
    for i, x in enumerate(json.load(open(FORMALMATH, encoding="utf-8"))):
        origenes.append(dict(id_origen=f"FormalMATH_lite[{i}]", fuente="FormalMATH-Lite",
                             subfuente=x.get("source"), nl=x["refined_statement"],
                             lean=x["autoformalization"], verdad_origen="verdadero (supuesto)",
                             contexto=""))
    for x in map(json.loads, open(CORPUS, encoding="utf-8")):
        if x["fuente"] not in ("formal_conjectures", "google-deepmind/formal-conjectures"):
            continue
        nl = doc_nl(x["contexto_lean"])
        if not nl:
            continue
        if not set(x.get("dependencias") or []) <= DEPS_OK:
            continue
        origenes.append(dict(id_origen=x["id"], fuente="formal_conjectures", subfuente=x.get("subfamilia"),
                             nl=nl, lean=x["enunciado_lean"], verdad_origen=x.get("verdad"),
                             contexto=x["contexto_lean"]))
    return origenes


# ---------------------------------------------------------------- tamaño de edición

class Contador:
    def __init__(self, sin_tokenizador=False):
        self.tok = None
        if not sin_tokenizador:
            os.environ.setdefault("HF_HUB_OFFLINE", "1")
            from transformers import AutoTokenizer
            self.tok = AutoTokenizer.from_pretrained(MODELO_TOK, revision=REVISION_TOK)

    def ids(self, s):
        if self.tok is None:
            return re.findall(r"\w+|[^\w\s]|\s+", s)
        return self.tok.encode(s, add_special_tokens=False)

    def editados(self, a, b):
        ia, ib = self.ids(a), self.ids(b)
        sm = difflib.SequenceMatcher(None, ia, ib, autojunk=False)
        quit = puest = tot = 0
        for op, i1, i2, j1, j2 in sm.get_opcodes():
            if op != "equal":
                quit += i2 - i1; puest += j2 - j1; tot += max(i2 - i1, j2 - j1)
        return tot, quit, puest, len(ia), len(ib)


def bin_de(t):
    for k, (a, b) in enumerate(BINS):
        if a <= t <= b:
            return k
    return len(BINS) - 1


def nombre_bin(k):
    a, b = BINS[k]
    return str(a) if a == b else (f"{a}+" if b >= 10**9 else f"{a}-{b}")


# ---------------------------------------------------------------- emparejamiento

def huellas(c):
    """Huellas superficiales que la edición añade (descriptivo; no entrena nada)."""
    o, v, nl = c["lean_original"], c["lean_variante"], c["nl"]
    h = []
    if len(re.findall(r"[₀-₉']", v)) > len(re.findall(r"[₀-₉']", o)):
        h.append("subindice_o_prima_nuevo")
    if v.count("¬") > o.count("¬"):
        h.append("negacion_nueva")
    nn = set(re.findall(r"\d+", nl))
    cuenta = lambda t: sum(n not in nn for n in re.findall(r"(?<![\w.])\d+(?![\w.])", t.split(":=")[0]))
    if cuenta(v) > cuenta(o):
        h.append("numeral_ausente_del_nl_nuevo")
    return h


def emparejar(cands, semilla=SEMILLA, max_pares=MAX_PARES_POR_ORIGEN, excluir=None):
    """Pares (infiel, fiel) dentro de cada origen.

    v1: mismo intervalo de tamaño de edición. Infieles en orden aleatorio (semilla), primero una por
    familia (A, B, C); para cada una, la fiel libre del mismo intervalo que (1) edita la misma clase
    de objeto (OBJETO), (2) comparte zona, (3) minimiza |Δ tokens|, (4) gana el sorteo.
    v2 (candidatos con `version` = 2): una infiel COMPUESTA «X∘D» se empareja solo con su propia D
    (`base_fiel`), si está libre; las infieles puras (A1, B1, B4, C1) se emparejan por intervalo como
    en v1 pero nunca con D1/D1c/D8 (SOLO_CON_COMPUESTAS). Las X puras no entran (EXCLUIR_DE_PARES_V2).
    Como mucho max_pares por origen; cada candidato en a lo sumo un par. Devuelve [(id_infiel, id_fiel)].
    """
    v2 = bool(cands) and cands[0].get("version", 1) >= 2
    if excluir is None:
        excluir = EXCLUIR_DE_PARES_V2 if v2 else EXCLUIR_DE_PARES
    por_origen = collections.defaultdict(list)
    for c in cands:
        por_origen[c["id_origen"]].append(c)
    pares = []
    for o in sorted(por_origen):
        cs = por_origen[o]
        inf = [c for c in cs if c["etiqueta_esperada"] == "inadecuada" and c["regla"] not in excluir]
        fie = [c for c in cs if c["etiqueta_esperada"] == "adecuada" and c["regla"] not in excluir]
        if not inf or not fie:
            continue
        rng_o = random.Random(f"{semilla}:{o}")
        rng_o.shuffle(inf)
        orden_f = {c["id"]: rng_o.random() for c in fie}
        vistas, primero, despues = set(), [], []
        for c in inf:
            (primero if c["familia"] not in vistas else despues).append(c)
            vistas.add(c["familia"])
        usadas, n = set(), 0
        for c in primero + despues:
            if n >= max_pares:
                break
            if c.get("base_fiel"):  # compuesta: solo con su propia D
                f = next((x for x in fie if x["id"] == c["base_fiel"] and x["id"] not in usadas), None)
                if f is None:
                    continue
            else:
                b = bin_de(c["tokens_editados"])
                # v2: las puras (A1, B1, B4, C1) admiten también el intervalo adyacente (preferido el
                # mismo), porque sus únicas parejas sin huella son D4h/D4c/D5 (ediciones grandes).
                tol = 1 if v2 else 0
                libres = [f for f in fie if f["id"] not in usadas
                          and abs(bin_de(f["tokens_editados"]) - b) <= tol
                          and not (v2 and f["regla"] in SOLO_CON_COMPUESTAS)]
                if not libres:
                    continue
                f = min(libres, key=lambda f: (abs(bin_de(f["tokens_editados"]) - b),
                                               not (objeto(f["regla"]) & objeto(c["regla"])),
                                               f["zona"] != c["zona"],
                                               abs(f["tokens_editados"] - c["tokens_editados"]),
                                               orden_f[f["id"]]))
            usadas.add(f["id"]); pares.append((c["id"], f["id"])); n += 1
    return pares


# ---------------------------------------------------------------- principal

def generar(sin_tokenizador=False):
    origenes = cargar_origenes()
    cont = Contador(sin_tokenizador)
    cands, aplicable, descartes = [], collections.Counter(), collections.Counter()
    analizables = 0
    def candidato(o, nl, lean, regla, s, var, base=None, base_fiel=None, sufijo_id=None):
        """Registro de un candidato. Para una compuesta (v2), `base` es la variante fiel D sobre la
        que se aplicó X: los tramos y los fragmentos son relativos a `base`; los tokens editados se
        cuentan respecto al original (y también respecto a la base)."""
        tot, q, pu, na, nb = cont.editados(lean, var)
        fam = familia(regla)
        c = dict(
            id=f"{o['id_origen']}::{sufijo_id or regla}", id_origen=o["id_origen"], fuente=o["fuente"],
            subfuente=o["subfuente"], archivo=archivo_de(o["id_origen"]), grupo=grupo_de(nl), nl=nl,
            lean_original=lean, lean_variante=var, regla=regla, familia=fam, familia_nombre=FAMILIA[fam],
            etiqueta_esperada=etiqueta(regla),
            direccion_trivial=DIRECCION_REGLA.get(regla.split("∘")[0], DIRECCION[fam]),
            zona=s["zona"], objeto=sorted(objeto(regla)), binder_editado=s["binder"],
            fragmento_original=s["frag_o"], fragmento_variante=s["frag_v"],
            tramos=[list(t) for t in s["tramos"]],
            tokens_editados=tot, tokens_quitados=q, tokens_puestos=pu,
            tokens_lean_original=na, tokens_lean_variante=nb,
            bin_edicion=nombre_bin(bin_de(tot)),
            correlato_nl=correlato(s["frag_o"] or s["frag_v"], nl),
            huellas=None,
            verdad_origen=o["verdad_origen"],
            extra={k: v for k, v in s.items() if k not in ("tramos", "zona", "binder", "frag_o", "frag_v")},
            version=3 if V3 else (2 if V2 else 1),
        )
        if V3 and regla.split("∘")[0] == "C2":
            d = direccion_c2(s["frag_o"], s.get("numeral"), s["zona"], s.get("pos_numeral"))
            c["direccion_c2_sintactica"] = bool(d)
            if d:
                c["direccion_trivial"], c["familia_sintactica"] = d
        if base is not None:
            c["lean_base"] = base
            c["base_fiel"] = base_fiel
            c["tokens_editados_vs_base"] = cont.editados(base, var)[0]
        return c

    vistos_lean = {}
    for o in origenes:
        nl, lean = o["nl"].strip(), o["lean"]
        if V3:
            if o["id_origen"] in EXCLUIR_ORIGENES_V3:
                descartes["v3_original_no_fiel"] += 1
                continue
            lean = neutralizar_nombre(lean)
        if not (NL_MIN <= len(nl) <= NL_MAX) or len(lean) > LEAN_MAX:
            descartes["longitud"] += 1
            continue
        if V2 and not nl_es_enunciado(nl):
            descartes["nl_no_es_enunciado"] += 1
            continue
        p = analizar(lean)
        if not p:
            descartes["no_analizable"] += 1
            continue
        if V3:
            clave = lean.strip()
            if clave in vistos_lean:
                descartes["v3_lean_duplicado_de_otro_origen"] += 1
                continue
            vistos_lean[clave] = o["id_origen"]
        analizables += 1
        del_origen = {}
        textos_origen = {}  # v3: lean_variante -> etiqueta, para no repetir variantes en un origen

        def repetida(c):
            if not V3:
                return False
            t = c["lean_variante"]
            if t in textos_origen:
                descartes["v3_variante_repetida" + ("" if textos_origen[t] == c["etiqueta_esperada"]
                                                    else "_etiqueta_distinta")] += 1
                return True
            textos_origen[t] = c["etiqueta_esperada"]
            return False
        for regla, f in REGLAS.items():
            try:
                sitios = f(lean, p, nl, o["contexto"]) if regla == "D3" else f(lean, p, nl)
            except Exception as e:  # una regla que falla no detiene el lote; se cuenta
                descartes[f"error_{regla}"] += 1
                continue
            if not sitios:
                continue
            s = sitios[0]
            var = aplicar(lean, s["tramos"])
            if var == lean:
                continue
            if analizar(var) is None:
                descartes[f"variante_no_analizable_{regla}"] += 1
                continue
            if V2 and familia(regla) != "D" and edicion_descartable(s["frag_v"], p, o["contexto"]):
                descartes[f"trivial_en_nat_{regla}"] += 1
                continue
            if V3 and regla == "D1" and s["zona"] == "conclusion":
                descartes["v3_D1_en_conclusion_igual_a_D1c"] += 1  # D1c la cubre
                continue
            c = candidato(o, nl, lean, regla, s, var)
            if repetida(c):
                continue
            aplicable[regla] += 1
            cands.append(c)
            del_origen[regla] = c
        if not V2:
            continue
        # v2: compuestas X∘D (X aplicada sobre la variante fiel D; primer sitio aplicable en la D)
        for d in COMPONER_D:
            if d not in del_origen:
                continue
            base = del_origen[d]["lean_variante"]
            pd = analizar(base)
            if pd is None:
                continue
            for x in COMPONER_X:
                if d not in COMPONER[x]:
                    continue
                try:
                    sitios = REGLAS[x](base, pd, nl)
                except Exception:
                    descartes[f"error_{x}∘{d}"] += 1
                    continue
                if not sitios:
                    descartes[f"compuesta_no_aplicable_{x}∘{d}"] += 1
                    continue
                s = sitios[0]
                var = aplicar(base, s["tramos"])
                if var == base or var == lean or analizar(var) is None:
                    descartes[f"compuesta_descartada_{x}∘{d}"] += 1
                    continue
                if edicion_descartable(s["frag_v"], pd, o["contexto"]):
                    descartes[f"trivial_en_nat_{x}∘{d}"] += 1
                    continue
                regla = f"{x}∘{d}"
                c = candidato(o, nl, lean, regla, s, var, base=base, base_fiel=del_origen[d]["id"])
                if repetida(c):
                    continue
                aplicable[regla] += 1
                cands.append(c)
    return origenes, analizables, cands, aplicable, descartes


def resumen(origenes, analizables, cands, aplicable, descartes, pares):
    por_regla = collections.defaultdict(list)
    for c in cands:
        por_regla[c["regla"]].append(c["tokens_editados"])
    fuentes = collections.Counter(o["fuente"] for o in origenes)
    def dist(v):
        return dict(n=len(v), mediana=statistics.median(v) if v else None,
                    media=round(statistics.mean(v), 2) if v else None,
                    bins={nombre_bin(k): sum(bin_de(t) == k for t in v) for k in range(len(BINS))})
    idx = {c["id"]: c for c in cands}
    inf_t = [idx[i]["tokens_editados"] for i, _ in pares]
    fie_t = [idx[f]["tokens_editados"] for _, f in pares]
    fam_pares = collections.Counter(idx[i]["familia"] for i, _ in pares)
    regla_pares = collections.Counter(idx[i]["regla"] for i, _ in pares)
    regla_pares_f = collections.Counter(idx[f]["regla"] for _, f in pares)
    misma_zona = sum(idx[i]["zona"] == idx[f]["zona"] for i, f in pares)
    mismo_objeto = sum(bool(objeto(idx[i]["regla"]) & objeto(idx[f]["regla"])) for i, f in pares)
    combos = collections.Counter(f'{idx[i]["regla"]}~{idx[f]["regla"]}' for i, f in pares)
    return dict(
        semilla=SEMILLA, origenes_por_fuente=dict(fuentes), origenes_analizables=analizables,
        descartes=dict(descartes),
        aplicables_por_regla=dict(aplicable),
        origenes_con_algun_candidato=len({c["id_origen"] for c in cands}),
        candidatos=len(cands),
        candidatos_por_etiqueta=dict(collections.Counter(c["etiqueta_esperada"] for c in cands)),
        candidatos_por_fuente_y_familia={f"{k[0]}|{k[1]}": v for k, v in sorted(
            collections.Counter((c["fuente"], c["familia"]) for c in cands).items())},
        tokens_por_regla={r: dist(v) for r, v in sorted(por_regla.items())},
        huellas_por_regla={r: {h: round(sum(h in c["huellas"] for c in cands if c["regla"] == r) /
                                        max(1, sum(c["regla"] == r for c in cands)), 3)
                               for h in ("subindice_o_prima_nuevo", "negacion_nueva", "numeral_ausente_del_nl_nuevo")}
                           for r in sorted(por_regla)},
        version=3 if V3 else (2 if V2 else 1),
        excluidas_de_pares=sorted(EXCLUIR_DE_PARES_V2 if V2 else EXCLUIR_DE_PARES),
        intervalos_tokens=[nombre_bin(k) for k in range(len(BINS))],
        archivos_con_candidato=len({c["archivo"] for c in cands}),
        tokens_infieles=dist([c["tokens_editados"] for c in cands if c["etiqueta_esperada"] == "inadecuada"]),
        tokens_fieles=dist([c["tokens_editados"] for c in cands if c["etiqueta_esperada"] == "adecuada"]),
        emparejamiento_provisional=dict(
            nota="Antes de certificar. El emparejamiento definitivo se rehace solo con candidatos certificados.",
            pares=len(pares), origenes_con_par=len({idx[i]["id_origen"] for i, _ in pares}),
            pares_por_familia_infiel=dict(fam_pares), pares_por_regla_infiel=dict(regla_pares),
            pares_por_regla_fiel=dict(regla_pares_f), misma_zona=misma_zona,
            mismo_objeto=mismo_objeto, combinaciones=dict(combos.most_common()),
            tokens_infiel=dist(inf_t), tokens_fiel=dist(fie_t),
            delta_abs_media=round(statistics.mean(abs(a - b) for a, b in zip(inf_t, fie_t)), 3) if pares else None,
            pares_compuestos=sum(bool(idx[i].get("base_fiel")) for i, _ in pares),
            archivos_con_par=len({idx[i]["archivo"] for i, _ in pares}),
            pares_por_fuente=dict(collections.Counter(idx[i]["fuente"] for i, _ in pares))),
    )


def main():
    global V2
    ap = argparse.ArgumentParser()
    ap.add_argument("--salida", default=AQUI)
    ap.add_argument("--sin_tokenizador", action="store_true")
    ap.add_argument("--v2", action="store_true",
                    help="lote v2 (filtros de NL, correlato de orden, compuestas X∘D): candidatos_v2.jsonl")
    ap.add_argument("--bases", nargs="+", default=None,
                    help="v2: restringir las bases fieles de las compuestas (p. ej. --bases D8 D4h D4c; "
                         "con solo D8 la compuerta de superficie dio 0,70 el 4 nov 2026). Cambia el sufijo del lote.")
    ap.add_argument("--v3", action="store_true",
                    help="lote v3 (v2 + los 7 cambios de las revisiones de muestra_30_v2): candidatos_v3.jsonl")
    a = ap.parse_args()
    global V3, COMPONER, COMPONER_X
    V3 = a.v3
    V2 = a.v2 or V3
    sufijo = "_v3" if V3 else ("_v2" if V2 else "")
    if V3:
        COMPONER = {k: v for k, v in COMPONER.items() if k != "B1"}
        COMPONER_X = tuple(COMPONER)
    if a.bases:
        global COMPONER_D
        COMPONER_D = tuple(b for b in COMPONER_D if b in set(a.bases))
        sufijo += "_" + "_".join(sorted(set(a.bases)))
    origenes, analizables, cands, aplicable, descartes = generar(a.sin_tokenizador)
    for c in cands:
        c["huellas"] = huellas(c)
    pares = emparejar(cands)
    enpar = {x for par in pares for x in par}
    for c in cands:
        c["en_emparejamiento_provisional"] = c["id"] in enpar
    ruta = os.path.join(a.salida, f"candidatos{sufijo}.jsonl")
    with open(ruta, "w", encoding="utf-8") as f:
        for c in cands:
            f.write(json.dumps(c, ensure_ascii=False) + "\n")
    R = resumen(origenes, analizables, cands, aplicable, descartes, pares)
    R["tokenizador"] = "regex (prueba)" if a.sin_tokenizador else f"{MODELO_TOK}@{REVISION_TOK}"
    R["sha256_candidatos"] = hashlib.sha256(open(ruta, "rb").read()).hexdigest()
    json.dump(R, open(os.path.join(a.salida, f"resumen_generacion{sufijo}.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)
    print(json.dumps({k: R[k] for k in ("origenes_por_fuente", "origenes_analizables", "aplicables_por_regla",
                                        "candidatos", "candidatos_por_etiqueta", "sha256_candidatos")},
                     ensure_ascii=False, indent=1))
    ep = R["emparejamiento_provisional"]
    print("pares provisionales:", ep["pares"], "| por familia:", ep["pares_por_familia_infiel"],
          "| |Δ| medio:", ep["delta_abs_media"])


if __name__ == "__main__":
    main()
