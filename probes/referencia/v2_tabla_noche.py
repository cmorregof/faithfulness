"""Tabla de la noche del 4 al 5 nov 2026 (prerregistro v2): lee v2_resultados_*.json y escribe una tabla
markdown. Holm PARCIAL sobre las 4 pruebas de la lectura (ii) de los modelos nuevos (la familia
prerregistrada son 8 pruebas; faltan las permutaciones de la lectura (i)). Solo lectura de resultados."""
import json
import os

AQUI = os.path.dirname(os.path.abspath(__file__))
NUEVOS = ["olmo2_7b", "gemma3_4b", "llama31_8b", "dsprover2_7b"]
OTROS = [("qwen3_4b_aleatorio", "control: pesos aleatorios"), ("qwen3_4b", "exploratorio / réplica fallida, recalculado"),
         ("goedel_8b", "exploratorio / réplica fallida, recalculado"), ("kimina_7b", "exploratorio / réplica fallida, recalculado")]


def f(x):
    return "—" if x is None else f"{x:+.3f}".replace(".", ",")


def g(x):
    return "—" if x is None else f"{x:.3f}".replace(".", ",")


def fila(n, rot, R):
    out = []
    for l, nom in (("i_ultimo_cv", "(i)"), ("ii_media_lean_capa_fija", "(ii)")):
        e = R["lecturas"][l]
        out.append(f"| {n} | {rot} | {nom} | {g(e['auroc_completo'])} | {g(e['auroc_solo_lean'])} | "
                   f"{f(e['delta'])} [{f(e['ic_delta'][0])}; {f(e['ic_delta'][1])}] | "
                   f"{f(e['completo_menos_apilado'])} [{f(e['ic_completo_menos_apilado'][0])}; {f(e['ic_completo_menos_apilado'][1])}] | "
                   f"{e['perm']['n']} | {g(e['perm']['p'])} |")
    return out


L = ["| Modelo | Rótulo | Lectura | AUROC completo | AUROC solo Lean | Δ [IC 95 %] | completo − apilado [IC 95 %] | n perm | p perm (sin corregir) |",
     "|---|---|---|---|---|---|---|---|---|"]
R = {}
for n in NUEVOS:
    p = os.path.join(AQUI, f"v2_resultados_{n}.json")
    if os.path.exists(p):
        R[n] = json.load(open(p, encoding="utf-8"))
        L += fila(n, "primario (nuevo)", R[n])
    else:
        L.append(f"| {n} | primario (nuevo) | — | sin resultados | | | | | |")
for n, rot in OTROS:
    p = os.path.join(AQUI, f"v2_resultados_{n}.json")
    if os.path.exists(p):
        L += fila(n, rot, json.load(open(p, encoding="utf-8")))
    else:
        L.append(f"| {n} | {rot} | — | sin resultados (no terminó) | | | | | |")
# Holm parcial, lectura (ii)
ps = [(n, R[n]["lecturas"]["ii_media_lean_capa_fija"]["perm"]["p"]) for n in NUEVOS if n in R]
orden = sorted(range(len(ps)), key=lambda i: ps[i][1])
aj, prev = {}, 0.0
for j, i in enumerate(orden):
    prev = max(prev, min(1.0, (len(ps) - j) * ps[i][1]))
    aj[ps[i][0]] = prev
L += ["", "Holm **parcial** sobre las 4 pruebas de la lectura (ii) de los modelos nuevos (con las 8 pruebas prerregistradas, los p ajustados solo pueden ser iguales o mayores):", ""]
for n, p in ps:
    ic = R[n]["lecturas"]["ii_media_lean_capa_fija"]["ic_completo_menos_apilado"]
    L.append(f"- {n}: p = {g(p)}, p Holm (4) = {g(aj[n])}, IC de completo − apilado entero > 0: {'sí' if ic[0] > 0 else 'no'}")
print("\n".join(L))
