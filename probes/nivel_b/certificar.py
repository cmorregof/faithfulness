"""Certificación con Lean de los candidatos del Nivel B. PREPARADO; NO LANZADO.

NO correr sin las aprobaciones de Carlos (ver lanzar.sh y reglas_generador.md): este script
elabora enunciados nuevos (las variantes) en Lean. Las variantes NO se intentan probar como
teoremas: solo se comparan con su original (equivalencia, una dirección, testigos).

Por candidato (original O, variante V), en un archivo .lean por enunciado de origen (cabecera +
contexto + un `example` por intento; cada intento tiene éxito si su `example` no da error):

  elabora_O / elabora_V   `example : Prop := ∀ binders, conclusión`
  Reescrituras fieles (D):
    equivalencia          local: `example <datos> : F_O ↔ F_V` (F = la hipótesis o la conclusión
                          editada) o global: `example : P_O ↔ P_V`, con tácticas estructurales
                          (Iff.rfl, simp only [lemas de notación], omega, intro/apply/assumption).
                          Ninguna de esas tácticas prueba el teorema mismo.
  Infieles (A, B, C):
    direccion             la implicación trivial de la regla (`P_V → P_O` o `P_O → P_V`)
    accidental            (solo ediciones de hipótesis) `example <datos> <demás hipótesis> :
                          F_O ↔ F_V`: si se prueba, la hipótesis editada era redundante y la
                          variante es EQUIVALENTE (se descarta). No toca la conclusión, así que no
                          depende de la verdad del teorema.
    testigo nivel 2       hipótesis: valores concretos que cumplen las demás hipótesis y separan
                          F_O de F_V; conclusión (A/C): valores que cumplen todas las hipótesis y
                          refutan la conclusión de V (V es falsa).
    testigo nivel 1       valores que separan F_O de F_V como fórmulas abiertas (sin hipótesis).
    plausible             (informativo) `plausible` sobre el objetivo de «accidental»; si halla
                          contraejemplo, sus valores se prueban como testigo en una segunda pasada.
  Estados: equivalente | no_equivalente (nivel 1 o 2) | equivalente_accidental | no_elabora |
           sin_decidir (con motivo). «sin_decidir» se cuenta aparte y no entra en el análisis.

Testigos: solo si todas las variables que aparecen son de tipo ℕ, ℤ, ℚ o ℝ; rejilla pequeña de
valores (los numerales del fragmento y ±1 primero), como mucho --max_testigos combinaciones, cada
una `⟨v1, …, by norm_num⟩`.

Paralelo: --procesos procesos de `lean` a la vez (uno por archivo), tiempo límite por archivo =
30 s + --timeout_caso × candidatos; si un archivo con varios candidatos se pasa, se reintenta
candidato por candidato. Reanudable: salta candidatos que ya están en <salida>/resultados.jsonl.
Opcional y desactivado: --goedel (Goedel-Prover-V2-8B local) para los «sin_decidir» de
equivalencia/dirección. NO PROBADO (no se puede cargar ningún modelo en esta sesión).

Comprobado SIN Lean el 4 nov 2026: sintaxis, construcción de archivos (--solo_archivos) y
--estimar. La prueba de punta a punta (--prueba_mathlib) espera la confirmación de Carlos:
  cd "/Users/cmorregof/Personal/Proyecto Godel" && \
  biblioteca/.venv/bin/python -I probes/nivel_b/certificar.py --prueba_mathlib --procesos 2 \
      --salida probes/nivel_b/prueba_mathlib
"""

import argparse
import collections
import concurrent.futures as cf
import datetime as dt
import itertools
import json
import os
import re
import subprocess
import sys
import threading
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generar as G  # noqa: E402

RAIZ = G.RAIZ
PROYECTO = os.path.join(RAIZ, "corpus_compilar", "corpus_lean")  # Mathlib + FormalConjecturesForMathlib
BITACORA = os.path.join(RAIZ, "probes", "BITACORA.md")
OPCIONES = ["set_option relaxedAutoImplicit false", "set_option maxSynthPendingDepth 3",
            "set_option autoImplicit false"]
HEARTBEATS = 200000
FIN = "FIN_CERTIFICAR"

TAC_DIR = [
    "intro h; intros; apply h <;> assumption",
    "intro h; intros; apply le_of_lt; apply h <;> assumption",
    "intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)",
    "intro h; intros; apply And.left; apply h <;> assumption",
    "intro h; intros; apply h <;> first | assumption | omega",
    "intro h; intros; apply h <;> first | assumption | linarith",
    "intro h; intros; aesop",  # se registra aparte: puede usar la verdad del enunciado
]
TAC_EQ_LOCAL = [
    "exact Iff.rfl", "exact and_comm", "exact not_lt.symm", "exact not_le.symm",
    "simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]",
    "omega", "constructor <;> intro _ <;> omega", "constructor <;> intro _ <;> linarith",
]
TAC_EQ_GLOBAL = [
    "exact Iff.rfl",
    "simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]",
    "simp only [and_comm]",
    "constructor <;> intro h <;> intros <;> apply h <;> assumption",
]
TAC_ACCID = [
    "omega", "constructor <;> intro _ <;> (first | trivial | omega)",
    "constructor <;> intro _ <;> (first | trivial | linarith)",
    "constructor <;> intro _ <;> (first | trivial | nlinarith)",
    "constructor <;> intro _ <;> (first | trivial | positivity)",
    "simp_all",
]
# v3 (revisión Fable de muestra_30_v2, cambio 2): comprobación de vacuidad del ORIGINAL, una vez por
# origen: `example <datos> <hipótesis> : False`. Si alguna táctica cierra, las hipótesis son
# inconsistentes, el original es vacuo y todos los candidatos del origen pasan a «origen_vacuo» (fuera
# del análisis). Solo usa las hipótesis, nunca la conclusión.
VAC = "__vacuidad__"
TAC_VACUO = ["linarith", "omega", "norm_num at *", "simp_all", "nlinarith"]
REJILLA = {"ℕ": ["0", "1", "2", "3", "5", "10"], "ℤ": ["0", "1", "-1", "2", "-2", "3"],
           "ℚ": ["0", "1", "-1", "2", "1/2", "3"], "ℝ": ["0", "1", "-1", "2", "1/2", "3"]}
ALIAS = {"Nat": "ℕ", "Int": "ℤ", "Rat": "ℚ", "Real": "ℝ"}


def ahora():
    return dt.datetime.now().astimezone().strftime("%Y-%m-%d %H:%M %Z")


def anotar(msg, bitacora):
    print(msg, flush=True)
    if bitacora:
        with open(BITACORA, "a", encoding="utf-8") as f:
            f.write(f"- [{ahora()}] certificar.py: {msg}\n")


# ---------------------------------------------------------------- piezas del enunciado

def universos(texto, cont):
    """Type*/Sort* -> Type u_cK (para escribir el enunciado como proposición ∀ …)."""
    def r(m):
        cont[0] += 1
        return f"{m.group(1)} u_c{cont[0]}"
    return re.sub(r"\b(Type|Sort)\*", r, texto)


def prop(p, cont):
    bs = " ".join(b["txt"] for b in p["binders"])
    cuerpo = f"∀ {bs}, {p['concl']}" if bs else p["concl"]
    return universos(cuerpo, cont)


def datos(p):
    return [b for b in p["binders"] if not b["hip"]]


def piezas(c):
    """F_O, F_V, hipótesis restantes (binders de O) y zona efectiva de un candidato."""
    po, pv = G.analizar(c["lean_original"]), G.analizar(c["lean_variante"])
    if po is None or pv is None:
        return None
    r, k = c["regla"], c["binder_editado"]
    hips_o = [b for b in po["binders"] if b["hip"]]
    if c["zona"] == "conclusion":
        return dict(po=po, pv=pv, FO=po["concl"], FV=pv["concl"], otras=hips_o, zona="conclusion")
    if r in ("D4h", "D6"):
        return dict(po=po, pv=pv, FO=None, FV=None, otras=hips_o, zona="global")
    # v2 (revisor Fable, 2026-11-04): las compuestas «X∘D» traen regla "A1∘D4h", etc. La familia y la
    # zona son las de X; `binder_editado` es un índice en la BASE (variante D), que coincide con el
    # del original salvo con D4h (reordena). Para A1 se localiza la hipótesis quitada por su texto.
    x = r.split("∘")[0]
    if x == "A1":
        b = next((bb for bb in po["binders"] if bb["txt"] == c["fragmento_original"]), None)
        if b is None and k is not None and k < len(po["binders"]):
            b = po["binders"][k]
        if b is None:
            return None
        return dict(po=po, pv=pv, FO=b["tipo"], FV="True", otras=[x_ for x_ in hips_o if x_ is not b],
                    zona="hipotesis")
    if x == "B1":
        return dict(po=po, pv=pv, FO="True", FV=pv["binders"][k]["tipo"], otras=hips_o, zona="hipotesis")
    if k is None or k >= len(po["binders"]) or len(po["binders"]) != len(pv["binders"]):
        return None
    b = po["binders"][k]
    if not b["hip"]:
        return None
    return dict(po=po, pv=pv, FO=b["tipo"], FV=pv["binders"][k]["tipo"],
                otras=[x for x in hips_o if x is not b], zona="hipotesis")


def vars_en(texto, p):
    """Variables de datos (en orden de declaración) que aparecen en el texto, con su tipo."""
    out = []
    for b in datos(p):
        for x in b["nombres"]:
            if re.search(r"(?<![\w.'])%s(?![\w'₀-₉])" % re.escape(x), texto):
                out.append((x, b["tipo"].strip()))
    return out


def combinaciones(vs, cuerpo, tope):
    nums = re.findall(r"(?<![\w.])\d+(?![\w.])", cuerpo)
    listas = []
    for _, t in vs:
        t = ALIAS.get(t, t)
        base = list(REJILLA[t])
        bord = []
        for n in nums:
            for d in (0, -1, 1):
                v = int(n) + d
                if v >= 0 or t != "ℕ":
                    bord.append(str(v))
        vals = list(dict.fromkeys(bord + base))
        listas.append(vals)
    if not vs:
        return [()]
    k = len(vs)
    m = max(2, int((4 * tope) ** (1 / k)))
    idx = sorted(itertools.product(*[range(min(m, len(l))) for l in listas]), key=lambda t: (sum(t), t))
    return [tuple(listas[j][i] for j, i in enumerate(t)) for t in idx[:tope]]


def literal(v, t):
    t = ALIAS.get(t, t)
    return f"({v} : {t})"


def testigos(vs, cuerpo, tope):
    """Lista de términos de prueba para `∃ vs, cuerpo` (o solo `cuerpo` si no hay variables)."""
    if any(ALIAS.get(t, t) not in REJILLA for _, t in vs):
        return None, []
    if not vs:
        return cuerpo, ["by norm_num", "by decide"]
    enun = "∃ " + " ".join(f"({x} : {t})" for x, t in vs) + ", " + cuerpo
    terms = []
    for combo in combinaciones(vs, cuerpo, tope):
        terms.append("⟨" + ", ".join(literal(v, t) for v, (_, t) in zip(combo, vs)) + ", by norm_num⟩")
    return enun, terms


def conj(partes):
    partes = [f"({x})" for x in partes if x and x != "True"]
    return " ∧ ".join(partes) if partes else "True"


# ---------------------------------------------------------------- construcción del archivo

class Archivo:
    def __init__(self):
        self.lineas, self.intentos = [], []  # intentos: (cand_id, chequeo, detalle, l0, l1)

    def add(self, texto):
        self.lineas.extend(texto.split("\n"))

    def ejemplo(self, cid, chequeo, detalle, texto):
        l0 = len(self.lineas) + 1
        self.add(f"set_option maxHeartbeats {HEARTBEATS} in\n" + texto)
        self.intentos.append((cid, chequeo, detalle, l0, len(self.lineas)))
        self.add("")

    def texto(self):
        return "\n".join(self.lineas) + "\n"


def cabecera_y_contexto(c, corpus):
    """Imports + opciones + contexto (sin el docstring final) + `open` del preámbulo."""
    imps, pre = ["Mathlib"], []
    if c["fuente"] == "formal_conjectures":
        fila = corpus[c["id_origen"]]
        if "FormalConjecturesForMathlib" in (fila.get("dependencias") or []):
            imps.append("FormalConjecturesForMathlib")
        ctx = fila["contexto_lean"].rstrip()
        k = ctx.rfind("/--")
        if ctx.endswith("-/") and k >= 0:
            ctx = ctx[:k].rstrip()
        pre.append(ctx)
    pre_lean = G.analizar(c["lean_original"])["pre"]
    for ln in pre_lean.splitlines():
        m = re.match(r"\s*import\s+(\S+)", ln)
        if m:
            # `import Mathlib` ya lo cubre todo; los submódulos de Mathlib que pide el original pueden no
            # existir en esta versión (FormalMATH_lite[324]: Mathlib.Algebra.BigOperators.Ring) y abortan el archivo.
            if m.group(1) not in imps and not m.group(1).startswith("Mathlib"):
                imps.append(m.group(1))
        elif ln.strip() and not ln.strip().startswith("@["):
            pre.append(ln)
    return "\n".join([f"import {m}" for m in imps] + OPCIONES) + "\n\n" + "\n".join(pre) + "\n"


def chequeos(arch, c, max_testigos, cont):
    pz = piezas(c)
    if pz is None:
        return "no_analizable"
    po, pv = pz["po"], pz["pv"]
    cid, fam = c["id"], c["familia"]
    PO, PV = prop(po, cont), prop(pv, cont)
    arch.ejemplo(cid, "elabora_O", "", f"example : Prop :=\n  {PO}")
    arch.ejemplo(cid, "elabora_V", "", f"example : Prop :=\n  {PV}")
    dat = " ".join(universos(b["txt"], cont) for b in datos(po))
    if fam == "D":
        if pz["zona"] != "global":
            for t in TAC_EQ_LOCAL:
                arch.ejemplo(cid, "equivalencia", f"local: {t}",
                             f"example {dat} :\n    ({pz['FO']}) ↔ ({pz['FV']}) := by\n  {t}")
        for t in TAC_EQ_GLOBAL:
            arch.ejemplo(cid, "equivalencia", f"global: {t}",
                         f"example :\n    ({PO}) ↔\n    ({PV}) := by\n  {t}")
        return None
    # --- infieles
    dirs = {"variante ⇒ original": [("V→O", PV, PO)], "original ⇒ variante": [("O→V", PO, PV)],
            "ninguna": [("V→O", PV, PO), ("O→V", PO, PV)]}[c["direccion_trivial"]]
    for nombre, a, b in dirs:
        for t in TAC_DIR:
            arch.ejemplo(cid, "direccion", f"{nombre}: {t}", f"example :\n    ({a}) →\n    ({b}) := by\n  {t}")
    FO, FV = pz["FO"], pz["FV"]
    otras = [b["tipo"] for b in pz["otras"]]
    if pz["zona"] == "hipotesis":
        hipb = " ".join(b["txt"] for b in pz["otras"])
        for t in TAC_ACCID:
            arch.ejemplo(cid, "accidental", t,
                         f"example {dat} {hipb} :\n    ({FO}) ↔ ({FV}) := by\n  {t}")
        arch.ejemplo(cid, "plausible", "",
                     f"example {dat} {hipb} :\n    ({FO}) ↔ ({FV}) := by\n  plausible")
        cuerpo2 = conj(otras + [f"¬(({FO}) ↔ ({FV}))"])
    elif fam in ("A", "C"):
        cuerpo2 = conj(otras + [f"¬({FV})"])
    else:
        cuerpo2 = None
    if cuerpo2:
        enun, terms = testigos(vars_en(cuerpo2, po), cuerpo2, max_testigos)
        for term in terms:
            arch.ejemplo(cid, "testigo2", term, f"example : {enun} :=\n  {term}")
    cuerpo1 = f"¬(({FO}) ↔ ({FV}))"
    enun, terms = testigos(vars_en(cuerpo1, po), cuerpo1, max_testigos)
    for term in terms:
        arch.ejemplo(cid, "testigo1", term, f"example : {enun} :=\n  {term}")
    return None


def construir(cands, corpus, max_testigos, extra=None):
    """Un archivo para un grupo de candidatos del mismo origen. extra: [(cid, chequeo, det, texto)]."""
    arch = Archivo()
    arch.add(cabecera_y_contexto(cands[0], corpus))
    cont = [0]
    malos = {}
    marca = len(arch.lineas)
    for c in cands:
        e = chequeos(arch, c, max_testigos, cont)
        if e:
            malos[c["id"]] = e
    for cid, chq, det, texto in (extra or []):
        arch.ejemplo(cid, chq, det, texto)
    po = G.analizar(cands[0]["lean_original"])
    if po is not None:
        hips = [b for b in po["binders"] if b["hip"]]
        if hips:
            dat = " ".join(universos(b["txt"], cont) for b in datos(po))
            hipb = " ".join(universos(b["txt"], cont) for b in hips)
            for t in TAC_VACUO:
                arch.ejemplo(VAC, "vacuidad", t, f"example {dat} {hipb} :\n    False := by\n  {t}")
    if cont[0]:
        arch.lineas.insert(marca, "universe " + " ".join(f"u_c{i}" for i in range(1, cont[0] + 1)))
        arch.intentos = [(a, b, d, l0 + 1, l1 + 1) for a, b, d, l0, l1 in arch.intentos]
    arch.add(f'#eval "{FIN}"')
    return arch, malos


# ---------------------------------------------------------------- Lean

class Lean:
    def __init__(self):
        r = subprocess.run(["lake", "env", "env"], cwd=PROYECTO, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit("lake env falló:\n" + r.stderr[-2000:])
        self.env = dict(l.split("=", 1) for l in r.stdout.splitlines() if "=" in l)
        ayuda = subprocess.run(["lean", "--help"], cwd=PROYECTO, env=self.env, capture_output=True, text=True).stdout
        self.json = "--json" in ayuda
        self.hilos = ["-j", "1"] if "--threads" in ayuda else []
        v = subprocess.run(["lean", "--version"], cwd=PROYECTO, env=self.env, capture_output=True, text=True).stdout
        self.version = v.strip()
        if "4.34.1" not in v:
            sys.exit("Toolchain distinto de 4.34.1; me detengo.")

    def correr(self, ruta, limite):
        t0 = time.time()
        try:
            r = subprocess.run(["lean", *(["--json"] if self.json else []), *self.hilos, "-DmaxErrors=1000000", str(ruta)],
                               cwd=PROYECTO, env=self.env, capture_output=True, text=True, timeout=limite)
        except subprocess.TimeoutExpired:
            return None, time.time() - t0
        msgs = []
        for ln in (r.stdout + "\n" + r.stderr).splitlines():
            if self.json and ln.startswith("{"):
                try:
                    j = json.loads(ln)
                    msgs.append({"sev": j.get("severity"), "linea": (j.get("pos") or {}).get("line", 0),
                                 "texto": (j.get("data") or "")[:2000]})
                    continue
                except json.JSONDecodeError:
                    pass
            m = re.match(r"^.*?:(\d+):(\d+): (error|warning|info)(?:\([^)]*\))?: ?(.*)$", ln)
            if m:
                msgs.append({"sev": m.group(3), "linea": int(m.group(1)), "texto": m.group(4)})
            elif "INTERNAL PANIC" in ln:  # Lean aborta el proceso (p. ej. «Nat.pow exponent is too big»)
                msgs.append({"sev": "panic", "linea": 0, "texto": ln[:500]})
            elif msgs and len(msgs[-1]["texto"]) < 2000:
                msgs[-1]["texto"] += "\n" + ln
        return msgs, time.time() - t0


def valores_plausible(texto):
    """Asignaciones «x := v» del mensaje de contraejemplo de plausible."""
    if "counter-example" not in texto.lower():
        return None
    return dict(re.findall(r"^\s*([^\s:]+)\s*:=\s*(.+?)\s*$", texto, re.M)) or None


class FalloLectura(RuntimeError):
    """Lean terminó un archivo pero no se leyó su resultado, o los veredictos no cuadran con los
    casos. Aborta la corrida: nunca se convierte en «sin_decidir»."""


ESTADOS = {"equivalente", "no_equivalente", "equivalente_accidental", "no_elabora", "sin_decidir",
           "origen_vacuo"}


def verificar_veredictos(res, cands, donde):
    """Un veredicto por caso, con los mismos id y un estado válido; si no, FalloLectura."""
    ids = [c["id"] for c in cands]
    if len(res) != len(ids) or set(res) != set(ids):
        faltan, sobran = sorted(set(ids) - set(res)), sorted(set(res) - set(ids))
        raise FalloLectura(f"{donde}: {len(res)} veredictos para {len(ids)} casos "
                           f"(faltan {faltan[:5]}, sobran {sobran[:5]})")
    malos = {cid: r.get("estado") for cid, r in res.items() if r.get("estado") not in ESTADOS}
    if malos:
        raise FalloLectura(f"{donde}: veredictos sin estado válido: {dict(list(malos.items())[:5])}")


def es_tiempo_agotado(r):
    return r.get("estado") == "sin_decidir" and r.get("motivo") == "tiempo agotado"


def verificar_tiempos(n_tiempo, n_casos, max_frac, donde):
    """Demasiados tiempos agotados = la corrida no está midiendo nada (p. ej. máquina saturada): aborta."""
    if n_casos and n_tiempo / n_casos > max_frac:
        raise FalloLectura(f"{donde}: {n_tiempo}/{n_casos} casos con tiempo agotado "
                           f"({n_tiempo / n_casos:.0%} > {max_frac:.0%}); subir --timeout_caso o bajar la "
                           f"carga de la máquina y reanudar (los tiempos agotados se reintentan)")


def interpretar(arch, msgs, cands, malos):
    errores = collections.defaultdict(list)
    avisos_sorry = collections.defaultdict(list)  # v3: advertencia «sorry» dentro de un intento = fallo
    fin = False
    primera = min((l0 for _, _, _, l0, _ in arch.intentos), default=10**9)
    err_ctx = []
    for m in msgs:
        if FIN in m["texto"] and m["sev"] in ("info", "information"):  # --json de Lean 4.34.1 da "information"
            fin = True
        if m["sev"] == "error":
            if m["linea"] < primera:
                err_ctx.append(m["texto"][:300])
            errores[m["linea"]].append(m["texto"])
        elif m["sev"] == "warning" and "sorry" in m["texto"]:
            avisos_sorry[m["linea"]].append(m["texto"])
    ok = collections.defaultdict(list)
    plaus = {}
    for cid, chq, det, l0, l1 in arch.intentos:
        errs = [t for l in range(l0, l1 + 1) for t in errores.get(l, []) + avisos_sorry.get(l, [])]
        if chq == "plausible":
            for t in errs:
                v = valores_plausible(t)
                if v:
                    plaus[cid] = v
            continue
        if not errs:
            ok[(cid, chq)].append(det)
    res = {}
    for c in cands:
        cid = c["id"]
        r = dict(id=cid, id_origen=c["id_origen"], regla=c["regla"], familia=c["familia"],
                 etiqueta_esperada=c["etiqueta_esperada"])
        fam_s = c.get("familia_sintactica") or c["familia"]  # v3: C2 con dirección sintáctica
        if c.get("familia_sintactica"):
            r["familia_sintactica"] = c["familia_sintactica"]
        if cid in malos:
            r.update(estado="sin_decidir", motivo=malos[cid]); res[cid] = r; continue
        if not fin:
            # Antes: «sin_decidir» y seguir. Así pasó en silencio el fallo de severidad del 4 nov
            # ("info" vs "information"): todo quedaba sin decidir y nada abortaba. Ahora aborta.
            ult = " | ".join(f"{m['sev']}@{m['linea']}: {m['texto'][:120]}" for m in msgs[-3:])
            raise FalloLectura(f"no se leyó la marca {FIN} ({len(msgs)} mensajes de Lean; "
                               f"últimos: {ult or 'ninguno'})")
        if err_ctx:
            r.update(estado="sin_decidir", motivo="error en cabecera/contexto", detalle=err_ctx[:2]); res[cid] = r; continue
        g = lambda k: ok.get((cid, k), [])
        r["elabora_O"], r["elabora_V"] = bool(g("elabora_O")), bool(g("elabora_V"))
        if not r["elabora_O"]:
            r.update(estado="sin_decidir", motivo="el original no elabora como proposición")
        elif not r["elabora_V"]:
            r.update(estado="no_elabora")
        elif c["familia"] == "D":
            e = g("equivalencia")
            r.update(estado="equivalente" if e else "sin_decidir", tacticas=e,
                     motivo=None if e else "ninguna táctica de equivalencia cerró")
        else:
            d = g("direccion")
            r["direccion_probada"] = bool(d)
            r["direccion_tacticas"] = d
            r["direccion_solo_aesop"] = bool(d) and all(x.endswith("aesop") for x in d)
            r["plausible_contraejemplo"] = plaus.get(cid)
            if g("accidental"):
                r.update(estado="equivalente_accidental", tacticas=g("accidental"))
            elif g("testigo2"):
                r.update(estado="no_equivalente", nivel=2, testigo=g("testigo2")[0])
            elif g("testigo1"):
                r.update(estado="no_equivalente", nivel=1, testigo=g("testigo1")[0])
            else:
                r.update(estado="sin_decidir", motivo="sin testigo (tipos no numéricos o rejilla agotada)")
            if c["zona"] == "conclusion" and c["familia"] in ("A", "C") and g("testigo2"):
                r["verdad_variante"] = "falsa (refutada)"
            elif fam_s == "B" and d:
                r["verdad_variante"] = "verdadera si el original lo es (dirección O⇒V probada)"
            else:
                r["verdad_variante"] = "desconocida"
        res[cid] = r
    vacuo = ok.get((VAC, "vacuidad"))
    if vacuo and fin and not err_ctx:
        for r in res.values():
            r["estado_sin_vacuidad"] = r.get("estado")
            r.update(estado="origen_vacuo", original_vacuo_tacticas=vacuo)
    return res


# ---------------------------------------------------------------- Goedel (desactivado)

def goedel_intentar(objetivos, modelo, revision, max_new_tokens=2048):
    """NO PROBADO. Devuelve {clave: prueba} para objetivos [(clave, texto_lean_sin_prueba)].
    Solo se usa con --goedel; carga el modelo local (prohibido en la sesión del 4 nov)."""
    import torch  # noqa: F401
    from transformers import AutoModelForCausalLM, AutoTokenizer
    tok = AutoTokenizer.from_pretrained(modelo, revision=revision)
    mod = AutoModelForCausalLM.from_pretrained(modelo, revision=revision, dtype="auto").eval()
    out = {}
    for clave, enun in objetivos:
        prompt = ("Complete the following Lean 4 code:\n\n```lean4\n" + enun + " := by\n```\n"
                  "Before producing the Lean 4 code, think briefly; then give the complete code.")
        ids = tok.apply_chat_template([{"role": "user", "content": prompt}], add_generation_prompt=True,
                                      return_tensors="pt")
        gen = mod.generate(ids, max_new_tokens=max_new_tokens, do_sample=False)
        txt = tok.decode(gen[0, ids.shape[1]:], skip_special_tokens=True)
        bloques = re.findall(r"```lean4?\n(.*?)```", txt, re.S)
        if bloques and ":= by" in bloques[-1]:
            out[clave] = bloques[-1].split(":= by", 1)[1]
    return out


# ---------------------------------------------------------------- prueba con Mathlib

def casos_mathlib():
    """Enunciados que YA están en Mathlib (le_of_lt, Nat.pos_of_ne_zero) y variantes cuya relación
    con ellos es un lema de Mathlib (gt_iff_lt, not_le, ne_eq, Nat.one_le_iff_ne_zero/omega,
    le_of_lt). No son candidatos del generador."""
    L1 = "import Mathlib\n\ntheorem le_of_lt' (a b : ℝ) (h : a < b) : a ≤ b := by"
    L2 = "import Mathlib\n\ntheorem pos_of_ne_zero' (n : ℕ) (h : n ≠ 0) : 0 < n := by"
    casos = [
        ("ML1", L1, "D1", "(h : a < b)", "(h : b > a)", "hipotesis", 1),
        ("ML1", L1, "D7", "(h : a < b)", "(h : ¬(b ≤ a))", "hipotesis", 1),
        ("ML1", L1, "A3", "(h : a < b)", "(h : a ≤ b)", "hipotesis", 1),
        ("ML2", L2, "D2", "(h : n ≠ 0)", "(h : ¬(n = 0))", "hipotesis", 1),
        ("ML2", L2, "D8", ": 0 < n :=", ": 1 ≤ n :=", "conclusion", None),
        ("ML2", L2, "B2", ": 0 < n :=", ": 0 ≤ n :=", "conclusion", None),
    ]
    out = []
    for o, lean, regla, a, b, zona, k in casos:
        var = lean.replace(a, b)
        fam = regla[0]
        out.append(dict(id=f"mathlib:{o}::{regla}", id_origen=f"mathlib:{o}", fuente="prueba_mathlib",
                        nl="(prueba)", lean_original=lean, lean_variante=var, regla=regla, familia=fam,
                        etiqueta_esperada=G.etiqueta(regla),
                        direccion_trivial=G.DIRECCION_REGLA.get(regla, G.DIRECCION[fam]),
                        zona=zona, binder_editado=k))
    esperado = {"D1": "equivalente", "D7": "equivalente", "D2": "equivalente", "D8": "equivalente",
                "A3": "no_equivalente", "B2": "no_equivalente"}
    return out, esperado


# ---------------------------------------------------------------- principal

def cargar_corpus(ids):
    out = {}
    for x in map(json.loads, open(G.CORPUS, encoding="utf-8")):
        if x["id"] in ids:
            out[x["id"]] = x
    return out


def estimar(grupos, a):
    """Estimación (no medida) con tiempos típicos de Lean 4.34.1 + Mathlib en esta Mac."""
    n_arch = len(grupos)
    n_d = sum(c["familia"] == "D" for g in grupos.values() for c in g)
    n_i = sum(c["familia"] != "D" for g in grupos.values() for c in g)
    n_fc = sum(g[0]["fuente"] == "formal_conjectures" for g in grupos.values())
    # import Mathlib caliente 2,8 s (medido por compilar_v2.py; 15 s en frío); contexto de FC ~2 s;
    # ~0,1 s por `example` sencillo; D ~12 intentos; infiel ~20 intentos + testigos (~mitad numéricos).
    cpu = n_arch * 2.8 + n_fc * 2.0 + 0.1 * (n_d * 14 + n_i * (22 + 0.5 * 2 * a.max_testigos))
    return dict(archivos=n_arch, candidatos_D=n_d, candidatos_infieles=n_i, cpu_horas=round(cpu / 3600, 2),
                horas_con={p: round(cpu / 3600 / p * 1.15, 2) for p in (4, 6, 8)})


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidatos", default=os.path.join(G.AQUI, "candidatos.jsonl"))
    ap.add_argument("--salida", default=os.path.join(G.AQUI, "certificacion"))
    ap.add_argument("--procesos", type=int, default=4)
    ap.add_argument("--timeout_caso", type=int, default=60)
    ap.add_argument("--max_testigos", type=int, default=32)
    ap.add_argument("--max_frac_tiempo", type=float, default=0.05,
                    help="aborta si la fracción de casos con tiempo agotado la supera (durante la "
                         "corrida, a partir de --min_casos_tiempo casos; al cerrar, siempre)")
    ap.add_argument("--min_casos_tiempo", type=int, default=20)
    ap.add_argument("--reglas", nargs="+", default=None)
    ap.add_argument("--limite_origenes", type=int, default=None)
    ap.add_argument("--todos", action="store_true",
                    help="certificar todos los orígenes (por defecto: solo los que tienen par provisional)")
    ap.add_argument("--prueba_mathlib", action="store_true")
    ap.add_argument("--solo_archivos", action="store_true", help="escribe los .lean sin correr Lean")
    ap.add_argument("--estimar", action="store_true", help="solo cuenta y estima el tiempo")
    ap.add_argument("--goedel", action="store_true", help="NO PROBADO; desactivado por defecto")
    ap.add_argument("--goedel_modelo", default="Goedel-LM/Goedel-Prover-V2-8B")
    ap.add_argument("--goedel_revision", default=None)
    ap.add_argument("--bitacora", action="store_true")
    a = ap.parse_args()
    a.salida = os.path.abspath(a.salida)  # Lean corre con cwd=PROYECTO: una ruta relativa no se encontraría

    if a.prueba_mathlib:
        cands, esperado = casos_mathlib()
    else:
        cands = [json.loads(l) for l in open(a.candidatos, encoding="utf-8")]
        if a.reglas:
            cands = [c for c in cands if c["regla"] in a.reglas]
        esperado = None
    grupos = collections.OrderedDict()
    for c in cands:
        grupos.setdefault(c["id_origen"], []).append(c)
    if not a.todos and not a.prueba_mathlib:
        con_par = {c["id_origen"] for c in cands if c.get("en_emparejamiento_provisional")}
        grupos = collections.OrderedDict((k, v) for k, v in grupos.items() if k in con_par)
    if a.limite_origenes:
        grupos = collections.OrderedDict(list(grupos.items())[: a.limite_origenes])
    if a.estimar:
        print(json.dumps(estimar(grupos, a), ensure_ascii=False, indent=1))
        return

    os.makedirs(os.path.join(a.salida, "lean"), exist_ok=True)
    ruta_res = os.path.join(a.salida, "resultados.jsonl")
    hechos = set()
    if os.path.exists(ruta_res):
        # un caso que agotó el tiempo NO cuenta como hecho: al reanudar (p. ej. con más
        # --timeout_caso) se reintenta, y su nueva línea sustituye a la anterior al leer `todos`
        hechos = {r["id"] for r in map(json.loads, open(ruta_res, encoding="utf-8"))
                  if not es_tiempo_agotado(r)}
    pend = collections.OrderedDict((k, [c for c in v if c["id"] not in hechos]) for k, v in grupos.items())
    pend = collections.OrderedDict((k, v) for k, v in pend.items() if v)
    corpus = cargar_corpus({k for k in pend}) if not a.prueba_mathlib else {}

    def nombre(o, sufijo=""):
        return re.sub(r"[^A-Za-z0-9_.-]", "_", o)[:150] + sufijo + ".lean"

    if a.solo_archivos:
        for o, cs in pend.items():
            arch, malos = construir(cs, corpus, a.max_testigos)
            open(os.path.join(a.salida, "lean", nombre(o)), "w", encoding="utf-8").write(arch.texto())
        print(f"{len(pend)} archivos escritos en {os.path.join(a.salida, 'lean')} (sin correr Lean)")
        return

    lean = Lean()
    anotar(f"inicio: {lean.version}; {sum(map(len, pend.values()))} candidatos en {len(pend)} archivos; "
           f"{a.procesos} procesos; salida {os.path.relpath(a.salida, RAIZ)}", a.bitacora)
    cerrojo = threading.Lock()

    def guardar(res):
        with cerrojo, open(ruta_res, "a", encoding="utf-8") as f:
            for r in res.values():
                f.write(json.dumps(r, ensure_ascii=False) + "\n")

    def uno(o, cs, sufijo=""):
        arch, malos = construir(cs, corpus, a.max_testigos)
        ruta = os.path.join(a.salida, "lean", nombre(o, sufijo))
        open(ruta, "w", encoding="utf-8").write(arch.texto())
        msgs, seg = lean.correr(ruta, 30 + a.timeout_caso * len(cs))
        panic = [m["texto"] for m in (msgs or []) if m["sev"] == "panic"]
        if panic:
            # Un pánico de Lean (determinista, p. ej. un testigo con exponente enorme) mata el archivo
            # entero: se reintenta candidato por candidato y el que vuelva a provocarlo queda sin_decidir.
            if len(cs) > 1:
                res = {}
                for j, c in enumerate(cs):
                    res.update(uno(o, [c], f"__{j}"))
                return res
            return {cs[0]["id"]: dict(id=cs[0]["id"], id_origen=o, regla=cs[0]["regla"],
                                      familia=cs[0]["familia"], etiqueta_esperada=cs[0]["etiqueta_esperada"],
                                      estado="sin_decidir", motivo="pánico de Lean: " + panic[0][:200],
                                      segundos=round(seg, 1))}
        if msgs is None:
            if len(cs) > 1:
                res = {}
                for j, c in enumerate(cs):
                    res.update(uno(o, [c], f"__{j}"))
                return res
            return {cs[0]["id"]: dict(id=cs[0]["id"], id_origen=o, regla=cs[0]["regla"],
                                      familia=cs[0]["familia"], etiqueta_esperada=cs[0]["etiqueta_esperada"],
                                      estado="sin_decidir", motivo="tiempo agotado", segundos=round(seg, 1))}
        try:
            res = interpretar(arch, msgs, cs, malos)
        except FalloLectura as e:
            raise FalloLectura(f"{os.path.relpath(ruta, RAIZ)}: {e}") from None
        # segunda pasada: testigos sugeridos por plausible
        extra = []
        for c in cs:
            r = res[c["id"]]
            v = r.get("plausible_contraejemplo")
            if r.get("estado") == "sin_decidir" and v:
                pz = piezas(c)
                po = pz["po"]
                cuerpo = conj([b["tipo"] for b in pz["otras"]] + [f"¬(({pz['FO']}) ↔ ({pz['FV']}))"])
                vs = vars_en(cuerpo, po)
                if vs and all(x in v for x, _ in vs) and all(ALIAS.get(t, t) in REJILLA for _, t in vs):
                    enun = "∃ " + " ".join(f"({x} : {t})" for x, t in vs) + ", " + cuerpo
                    term = "⟨" + ", ".join(literal(v[x], t) for x, t in vs) + ", by norm_num⟩"
                    extra.append((c["id"], "testigo2", "plausible " + term, f"example : {enun} :=\n  {term}"))
        if extra:
            arch2, malos2 = construir(cs, corpus, 0, extra)
            ruta2 = ruta.replace(".lean", "__plausible.lean")
            open(ruta2, "w", encoding="utf-8").write(arch2.texto())
            msgs2, seg2 = lean.correr(ruta2, 30 + a.timeout_caso * len(cs))
            if msgs2 is not None:
                try:
                    res2 = interpretar(arch2, msgs2, cs, malos2)
                except FalloLectura as e:
                    raise FalloLectura(f"{os.path.relpath(ruta2, RAIZ)}: {e}") from None
                for cid, r2 in res2.items():
                    if res[cid].get("estado") == "sin_decidir" and r2.get("estado") == "no_equivalente":
                        res[cid].update(estado="no_equivalente", nivel=r2["nivel"], testigo=r2["testigo"],
                                        via="plausible")
                seg += seg2
        for r in res.values():
            r["segundos_archivo"] = round(seg, 1)
            r["archivo"] = os.path.relpath(ruta, RAIZ)
        verificar_veredictos(res, cs, os.path.relpath(ruta, RAIZ))
        return res

    t0, n = time.time(), 0
    n_casos = n_tiempo = 0
    ex = cf.ThreadPoolExecutor(max_workers=a.procesos)
    futs = {ex.submit(uno, o, cs): o for o, cs in pend.items()}
    try:
        for fu in cf.as_completed(futs):
            res = fu.result()
            verificar_veredictos(res, pend[futs[fu]], futs[fu])
            guardar(res)
            n += 1
            n_casos += len(res)
            n_tiempo += sum(map(es_tiempo_agotado, res.values()))
            if n_casos >= a.min_casos_tiempo:
                verificar_tiempos(n_tiempo, n_casos, a.max_frac_tiempo, f"tras {n} archivos")
            if n % 50 == 0 or n == len(futs):
                anotar(f"avance: {n}/{len(futs)} archivos; {time.time() - t0:.0f} s", a.bitacora and n % 200 == 0)
    except FalloLectura as e:
        ex.shutdown(wait=False, cancel_futures=True)
        subprocess.run(["pkill", "-TERM", "-P", str(os.getpid())])  # los `lean` aún en marcha
        anotar(f"ABORTADO tras {n}/{len(futs)} archivos guardados: {e}", a.bitacora)
        sys.exit(3)  # no se escribe resumen.json; los archivos anteriores ya guardados se conservan
    ex.shutdown()

    if a.goedel:
        anotar("--goedel pedido: NO PROBADO; se deja sin ejecutar en esta versión.", a.bitacora)

    todos = {}
    for l in open(ruta_res, encoding="utf-8"):
        r = json.loads(l)
        todos[r["id"]] = r
    try:  # el total también: un veredicto por cada caso pedido (resultados.jsonl puede traer otros
        #   de corridas anteriores con otro filtro; esos no cuentan aquí)
        pedidos = [c for g in grupos.values() for c in g]
        mios = {c["id"]: todos[c["id"]] for c in pedidos if c["id"] in todos}
        verificar_veredictos(mios, pedidos, ruta_res)
        verificar_tiempos(sum(map(es_tiempo_agotado, mios.values())), len(mios), a.max_frac_tiempo,
                          "al cerrar (total de casos pedidos)")
    except FalloLectura as e:
        anotar(f"ABORTADO al cerrar: {e}", a.bitacora)
        sys.exit(3)
    cuenta = collections.Counter((r["regla"], r["estado"]) for r in todos.values())
    resumen = dict(lean=lean.version, segundos=round(time.time() - t0, 1),
                   por_regla_y_estado={f"{k[0]}|{k[1]}": v for k, v in sorted(cuenta.items())},
                   por_estado=dict(collections.Counter(r["estado"] for r in todos.values())))
    if esperado:
        resumen["prueba_mathlib"] = {cid: dict(obtenido=r["estado"], esperado=esperado[r["regla"]],
                                               ok=r["estado"] == esperado[r["regla"]])
                                     for cid, r in todos.items()}
        resumen["prueba_mathlib_ok"] = all(v["ok"] for v in resumen["prueba_mathlib"].values())
    json.dump(resumen, open(os.path.join(a.salida, "resumen.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=1)
    anotar(f"fin: {resumen['por_estado']}" + (f"; prueba_mathlib_ok={resumen.get('prueba_mathlib_ok')}"
                                              if esperado else ""), a.bitacora)


if __name__ == "__main__":
    main()
