#!/usr/bin/env python3
"""verifica_v5.py — comprueba v5_causal contra v4_voz (13 nov 2026). Adaptación de verifica_voz.py.

Fuera de los pasajes aprobados, cifras, claves \\cite/\\ref/\\label, fórmulas, tablas y figuras deben ser idénticas a
v4_voz. Dentro de ellos, cada cifra nueva debe salir de tablas_nivel_b.json (lo que escribe tablas_nivel_b.py), de
ablacion.json o de comprobacion_causal.json (S1), o ser un entero estructural de la lista ESTRUCTURALES.
Sale con código 1 si algo falla.   Uso (desde v5_causal):  python3 verifica_v5.py
"""
import glob, json, math, os, re, sys
from collections import Counter

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.join(AQUI, "..", "..")
V = {}
exec(open(os.path.join(AQUI, "verifica_voz.py"), encoding="utf-8").read().split("def main")[0], V)
MENOS = "−"
# enteros que no son resultados: nº de direcciones, pares, pares sin C2, nivel del intervalo, fechas, dosis,
# umbral de azar, y medidas de formato de las tablas (\vspace{2pt}, \tabcolsep{3pt})
ESTRUCTURALES = {"20", "377", "309", "95", "11", "12", "13", "0.5", "2", "3", "4", "6", "0"}
NUEVAS = {"label": {"tab:bcontroles2", "tab:bintervencion", "fig:bintervencion", "app:intervencion", "tab:bsecundarios", "tab:bejemplos", "app:definiciones", "tab:bsinc2"},
          "ref": {"tab:bcontroles2", "tab:bintervencion", "fig:bintervencion", "tab:controlesnivel", "app:intervencion", "tab:bsecundarios", "tab:a", "tab:conjunta", "tab:b", "tab:bejemplos", "app:definiciones", "tab:bsinc2"},
          "cite": {"geometry", "elazar2021amnesic", "rimsky2024steering", "ravfogel2020null", "belrose2023leace", "makelov2024subspace", "xena2026checked", "bastounis2026lost"}}
FORMULAS_NUEVAS = {"\\D": 2, "C = 1": 1, "\\neq": 1, "p": 2}   # undécima tanda: $\D$ en la regla del Nivel C y ante la cifra de la segunda implementación
TABLAS_EDITADAS = ("tab:controles}", "tab:conjunta}", "tab:b}")   # tab:b: dos frases en el pie (novena tanda)


def hojas(o):
    if isinstance(o, dict):
        for v in o.values(): yield from hojas(v)
    elif isinstance(o, list):
        for v in o: yield from hojas(v)
    elif isinstance(o, (int, float)) and not isinstance(o, bool):
        yield o


def permitidas():
    s = set()
    for ruta in (os.path.join(RAIZ, "probes", "intervencion", "resultados_s5", "tablas_nivel_b.json"),
                 os.path.join(RAIZ, "probes", "intervencion", "resultados", "qwen3_4b", "ablacion.json")):
        for x in hojas(json.load(open(ruta, encoding="utf-8"))):
            t = f"{abs(x):.3f}"
            s |= {t, "+" + t, MENOS + t}
            if isinstance(x, int): s.add(str(x))
    cos = min(json.load(open(f))[k]["coseno_min"]
              for f in glob.glob(os.path.join(RAIZ, "probes", "activaciones", "sin_pregunta", "*", "comprobacion_causal.json"))
              if "prueba" not in f for k in ("completo_media_lean", "solo_lean_media_lean"))
    s5 = json.load(open(os.path.join(RAIZ, "probes", "intervencion", "resultados_s5", "tablas_nivel_b.json"), encoding="utf-8"))["s5"]
    if max(abs(d["placebo"] - d["base"][0]) for d in s5.values()) < 0.02:
        s.add("0.02")                               # «within 0.02 of the base»: cota del placebo, comprobada aquí
    s6 = json.load(open(os.path.join(RAIZ, "probes", "intervencion", "resultados_s5", "s6_masa.json"), encoding="utf-8"))
    for x in hojas(s6):
        if isinstance(x, float): s.add(f"{abs(x):.3f}")
    if min(d["base"][0] for d in s6.values()) >= 0.982:
        s.add("0.982")                              # «at least 0.982»: masa mínima sin intervenir
    if all(abs(v - d["base"][0]) < 0.001 for d in s6.values() for k in ("f2", "f4", "f8")
           for v in (d[k]["sonda"][0], d[k]["azar_min"], d[k]["azar_max"])):
        s.add("0.001")                              # el desplazamiento cambia la masa en menos de 0.001
    s.add("5")                                      # cinco direcciones al azar en las dosis
    # sexta tanda: apilado, lean_only y nl_only de la lectura (ii) del Nivel A, y las exclusiones del Nivel B
    for m in ("olmo2_7b", "gemma3_4b", "llama31_8b", "dsprover2_7b"):
        e = json.load(open(os.path.join(RAIZ, "probes", "referencia", f"v2_resultados_{m}.json"), encoding="utf-8"))["lecturas"]["ii_media_lean_capa_fija"]
        s |= {f"{e[k]:.3f}" for k in ("apilado", "auroc_solo_lean", "auroc_solo_nl")}
        s.add(str(json.load(open(os.path.join(RAIZ, "probes", "referencia", f"v2_resultados_{m}.json"), encoding="utf-8"))["n"]))  # «the 450 that compile»
        for z in [e["sensibilidad_sin_dudosas"]["delta_sobre_puntajes_del_primario"], *e["sensibilidad_sin_dudosas"]["ic"]]:
            t = f"{abs(z):.3f}"                         # undécima tanda: intervalos de la sensibilidad sin dudosas
            s |= {t, "+" + t, MENOS + t}
    s.add(str(sum(1 for _ in open(os.path.join(RAIZ, "probes", "activaciones", "dsprover2_7b", "manifiesto.jsonl"), encoding="utf-8"))))  # «500 rows»
    exc = json.load(open(os.path.join(RAIZ, "probes", "nivel_b", "datos", "exclusiones_nivel_b.json"), encoding="utf-8"))
    ob, eq = set(exc["excluir_obligatorio"]["pares"]), set(exc["excluir_del_principal_reportar_aparte"]["pares"])
    if len(ob & eq) == 1 and len(ob | eq) == exc["pares_totales"] - exc["pares_analisis_principal"]:
        s |= {str(len(ob)), str(len(eq)), str(len(ob | eq))}   # «9», «23» y «31»; un par está en los dos grupos
    # novena tanda: bootstrap por archivo fuente del Nivel B y brecha del Nivel A sin la pregunta
    for m in ("qwen3_4b", "olmo2_7b", "llama31_8b", "gemma3_4b"):
        pa = json.load(open(os.path.join(RAIZ, "probes", "nivel_b", "resultados", f"nivel_b_{m}_principal.json"), encoding="utf-8"))
        sp = json.load(open(os.path.join(RAIZ, "probes", "sin_pregunta", "resultados", f"s2a_{m}.json"), encoding="utf-8"))
        s.add(str(pa["n_archivos"]))                 # «189 source files», la unidad de esa sensibilidad
        for x in pa["secundarios"]["central_bootstrap_por_archivo"]["diferencia"] + sp["sin_pregunta"]["delta_sp"]:
            t = f"{abs(x):.3f}"
            s |= {t, "+" + t, MENOS + t}
    # decimoquinta tanda: S7 (Holm e intervención sin C2), escrito por s7_sin_c2.py con la regla aprobada
    for z in hojas(json.load(open(os.path.join(RAIZ, "probes", "intervencion", "resultados_s5", "s7_sin_c2.json"), encoding="utf-8"))):
        t = f"{abs(z):.3f}"
        s |= {t, "+" + t, MENOS + t}
        if isinstance(z, int): s.add(str(z))
    cs = json.load(open(os.path.join(RAIZ, "probes", "nivel_b", "datos", "compuerta_superficie_certificados.json"), encoding="utf-8"))
    if cs["criterio"] == "firma" and not cs["pasa"]:       # séptima tanda: compuerta de superficie
        s |= {f"{cs['auroc_pareada_solo_lean']:.3f}", f"{cs['exceso_firma']:.3f}", f"{cs['umbral_firma']:.2f}", str(cs["n_pares"])}
    s.add(f"{math.floor(cos * 1e4) / 1e4:.4f}")     # «at least 0.9993»: el mínimo truncado a cuatro decimales
    return s, cos


def ejemplos(nuevo, falla):
    """Décima tanda: tab:bejemplos. Sus dígitos son texto Lean y enunciados citados, no cifras del artículo, así que
    la tabla sale del conteo de cifras y se comprueba aquí contra el índice de pares: la selección repite la regla,
    los fragmentos son los del índice y cada fila del .tex es la que se arma desde ejemplos_nivel_b.json."""
    sys.path.insert(0, AQUI)
    import ejemplos_nivel_b as E
    tab = [t for t in re.findall(r"\\begin\{table\}.*?\\end\{table\}", nuevo, re.S) if r"\label{tab:bejemplos}" in t]
    if len(tab) != 1: falla("tab:bejemplos no aparece exactamente una vez"); return nuevo
    sel, js = E.seleccion(), json.load(open(os.path.join(AQUI, "ejemplos_nivel_b.json"), encoding="utf-8"))
    if [e["familia"] for e in js] != list(E.FAMILIAS): falla("tab:bejemplos: familias")
    for e in js:
        k, suma, emp, f, i = sel[e["familia"]]
        if (e["par"], e["suma_tokens_editados"], e["pares_empatados"]) != (k, suma, emp): falla(f"tab:bejemplos {e['familia']}: el par no es el de la regla")
        if e["fiel"] != {"original": f["fragmento_original"], "variante": f["fragmento_variante"]} or \
           e["infiel"] != {"original": i["fragmento_original"], "variante": i["fragmento_variante"]}:
            falla(f"tab:bejemplos {e['familia']}: fragmentos distintos de los del índice")
        if e["enunciado_hasta"] and not e["enunciado"].startswith(e["enunciado_hasta"]): falla(f"tab:bejemplos {e['familia']}: recorte")
    if V["norm"](E.filas_tex()) not in V["norm"](tab[0]): falla("tab:bejemplos: las filas del .tex no son las del JSON")
    print(f"   tab:bejemplos: pares {[e['par'] for e in js]}, fragmentos iguales a los del índice")
    return nuevo.replace(tab[0], "")


def revisa(nombre):
    viejo, nuevo = V["lee"](os.path.join(AQUI, "..", "v4_voz", nombre)), V["lee"](os.path.join(AQUI, nombre))
    ok = True
    def falla(msg):
        nonlocal ok; ok = False; print("   FALLA:", msg)
    print(f"== {nombre}")
    perm, cos = permitidas()
    # 1. cifras (todo el documento, resumen incluido)
    sin_nombres = lambda x: re.sub(r"Llama-3\.1(?:-8B)?|OLMo-2(?:-7B)?|Qwen3-\dB|Gemma-3(?:-4B)?|LLaMA-2|bfloat16|\\cite[tp]?\{[^}]*\}", " ", x)
    # decimosexta tanda: las dos cifras de la frase de la introducción (290 y 38) son del post citado, no de nuestros
    # datos. Se sacan del conteo solo dentro de esa frase, que debe aparecer exactamente una vez.
    cita = re.compile(r"(?:Of some 290 Lean-bearing papers|De unos 290 artículos con Lean)[^.]*?\\citep\{xena2026checked\}")
    if len(cita.findall(nuevo)) != 1: falla("la frase que cita el post de Xena no aparece exactamente una vez")
    nuevo_sin_cita = cita.sub(" ", nuevo)
    # decimonovena tanda: el identificador del commit del repositorio («ea66bad») no es una cifra. Se saca del conteo
    # solo en esa forma exacta, que debe aparecer exactamente una vez, en «Code and data».
    commit = re.compile(r"commit\s+\\vr\{[0-9a-f]{7}\}")
    if len(commit.findall(nuevo)) != 1: falla("el commit del repositorio no aparece exactamente una vez")
    nuevo_sin_cita = commit.sub(" ", nuevo_sin_cita)
    sv, sn = V["dif"](V["numeros"](sin_nombres(viejo)), V["numeros"](sin_nombres(ejemplos(nuevo_sin_cita, falla))))
    # decimoctava tanda: la segunda implementación del Nivel C pasa de cinco a tres decimales, por redondeo
    REDONDEADAS = {"+0.15354": "+0.154", "0.12102": "0.121", "0.18714": "0.187"}
    for vieja, nueva in REDONDEADAS.items():
        s_ = "+" if vieja.startswith("+") else ""
        if f"{s_}{float(vieja):.3f}" != nueva: falla(f"redondeo mal hecho: {vieja} -> {nueva}")
        if sv.get(vieja) == 1 and sn.get(nueva, 0) >= 1:
            del sv[vieja]; sn[nueva] -= 1
            if not sn[nueva]: del sn[nueva]
    if sv: falla(f"cifras de v4 que ya no están: {sv}")
    fuera = {k: n for k, n in sn.items() if k not in perm and k not in ESTRUCTURALES}
    if fuera: falla(f"cifras nuevas sin fuente: {fuera}")
    print(f"   cifras nuevas: {sum(sn.values())} apariciones, {len(sn)} distintas; sin fuente: {len(fuera)}; coseno mínimo S1 = {cos:.5f}")
    # 2. claves
    for orden in ("label", "ref", "cite", "citet", "citep"):
        a, b = V["dif"](V["claves"](viejo, orden), V["claves"](nuevo, orden))
        extra = set(b) - NUEVAS["cite" if orden.startswith("cite") else orden]
        if a or extra: falla(f"\\{orden}: faltan {a}, sobran {extra}")
    # 3. fórmulas fuera de tablas y figuras
    a, b = V["dif"](V["matematicas"](viejo), V["matematicas"](nuevo))
    b = {k: n for k, n in b.items() if n != FORMULAS_NUEVAS.get(k)}
    if a or b: falla(f"fórmulas: faltan {a}, sobran {b}")
    # 4. tablas y figuras de v4: idénticas, salvo las dos tablas con un retoque aprobado
    for env in ("table", "figure"):
        ev, en = V["entornos"](viejo, env), V["entornos"](nuevo, env)
        if env == "figure":   # decimocuarta tanda: fig:escaner cambia de archivo y de [t] a [p]; el pie debe ser idéntico
            def v4(e):
                if "label{fig:escaner}" not in e: return e
                if not re.search(r"\\begin\{figure\}\[p\] \\centering \\includegraphics\[width=\\linewidth\]\{figuras_v5/escaner2d_modelos_v5(_es)?\.pdf\}", e):
                    falla("fig:escaner: no es la figura aprobada"); return e
                return e.replace("[p]", "[t]", 1).replace("figuras_v5/escaner2d_modelos_v5", "figuras_v3/escaner2d_modelos", 1)
            en = [v4(e) for e in en]
        # decimosexta tanda: «the Lean alone» pasa a «the Lean code alone» (y «Lean solo» a «código de Lean solo») también en los pies
        en = [e.replace("the Lean code alone", "the Lean alone").replace("código de Lean solo", "Lean solo") for e in en]
        # decimoctava tanda: «the Lean» suelto pasa a «the Lean code» y «el/del/al Lean» a «… código de Lean»
        en = [e.replace("the Lean code", "the Lean").replace("l código de Lean", "l Lean") for e in en]
        falt = [e for e in ev if e not in en and not any(t in e for t in TABLAS_EDITADAS)]
        if falt: falla(f"{env} de v4 cambiado: {[e[:60] for e in falt]}")
        nuevos = [e for e in en if e not in ev]
        print(f"   {env}: {len(ev)} en v4, {len(en)} en v5, nuevos o editados: {len(nuevos)}")
    # 5. resumen
    res, _ = V["parte"](nuevo)
    n = V["palabras"](res)
    if not 150 <= n <= 250: falla(f"resumen de {n} palabras")
    salv = [("did not pass", "no pasó"), ("Exploratory maps", "mapas exploratorios"), ("No level alone supports", "Ningún nivel sostiene por sí solo")]
    r1 = re.sub(r"\s+", " ", res)
    for en_, es_ in salv:
        if en_ not in r1 and es_ not in r1: falla(f"falta la salvedad «{en_}» en el resumen")
    print(f"   resumen: {n} palabras; cifras: {sorted(set(V['NUM'].findall(res)))}")
    # 6. frases que delimitan la evidencia y giros prohibidos
    for fr in V["FRASES"]:
        cv, cn = viejo.count(fr), nuevo.count(fr)
        if cv or cn: print(f"   «{fr}»: v4 {cv}, v5 {cn}" + ("   <-- baja" if cn < cv else ""))
    for p in V["PROHIBIDO"]:
        if nuevo.lower().count(p.lower()) > viejo.lower().count(p.lower()): falla(f"giro prohibido nuevo: {p!r}")
    for p in ("replication of the intervention", "preregistered intervention"):
        if p in nuevo: falla(p)
    print("   RESULTADO:", "pasa" if ok else "NO PASA")
    return ok


if __name__ == "__main__":
    sys.exit(0 if all([revisa("main_en.tex"), revisa("main_es.tex")]) else 1)
