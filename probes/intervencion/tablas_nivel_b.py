"""Cifras del Nivel B para el artículo, recalculadas con toda la precisión (13 nov 2026).

Por qué existe: s5.json guarda las cifras de S5 con cuatro decimales, y redondear a tres desde ahí puede dar un
milésimo distinto del que sale de los datos. Este guion rehace el análisis de intercambio.py (mismo remuestreo,
misma semilla) sin redondear, comprueba que coincide con s5.json a cuatro decimales y solo entonces escribe las
cifras a tres decimales. Las de S3 se leen de s3_<modelo>.json, que ya guarda toda la precisión.

No corre ningún modelo ni cambia ningún resultado. Escribe probes/intervencion/resultados_s5/tablas_nivel_b.json
y, con --latex, imprime las filas listas para las tablas (formato del artículo).

Uso (desde la raíz de Proyecto Godel):  $PY -I probes/intervencion/tablas_nivel_b.py [--latex]
"""
import argparse
import json
import os
import sys

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import intercambio as S  # noqa: E402

MODELOS = [("qwen3_4b", "Qwen3-4B"), ("olmo2_7b", "OLMo-2-7B"), ("llama31_8b", "Llama-3.1-8B"), ("gemma3_4b", "Gemma-3-4B")]
MENOS = "−"


def s5_sin_redondear(nombre):
    import ablacion as A
    import analizar_pares as AP
    carpeta, indice, salida = S.rutas(nombre)
    tren, sel, y, g, pares, gp = A.cargar_pares(carpeta, indice)
    P = np.load(os.path.join(salida, "pyes.npy"))
    nombres = [c[0] for c in S.condiciones()]
    assert P.shape == (len(nombres), len(y), 4) and np.load(os.path.join(salida, "hecho.npy")).all()
    j = {n: k for k, n in enumerate(nombres)}
    az = lambda pref: [j[n] for n in nombres if n.startswith(pref + "_azar")]
    Sc = P[:, :, 0] / np.maximum(P[:, :, 0] + P[:, :, 1], 1e-12)
    W = np.array([AP.por_origen(AP.w_pares(s, pares), gp) for s in Sc])
    auc = W.mean(1)
    m = W.shape[1]
    idx = np.random.default_rng(0).integers(0, m, (S.N_BOOT, m))
    rW = np.array([W[:, ix].mean(1) for ix in idx])
    ic = lambda v: [float(x) for x in np.percentile(v, [2.5, 97.5])]
    caida = auc[0] - auc

    def fam(cond, pref):
        c, azar = j[cond], az(pref)
        return {"auroc": float(auc[c]), "auroc_ic": ic(rW[:, c]), "caida": [float(caida[c]), *ic(rW[:, 0] - rW[:, c])],
                "caidas_azar": [float(x) for x in caida[azar]], "auroc_azar": [float(x) for x in auc[azar]],
                "azar_media": float(caida[azar].mean()), "azar_max": float(caida[azar].max()),
                "menos_azar": [float(caida[c] - caida[azar].mean()), *ic(rW[:, azar].mean(1) - rW[:, c])],
                "supera_a_todas": bool((caida[c] > caida[azar]).all()),
                "n_azar_iguales_o_mayores": int((caida[azar] >= caida[c]).sum()), "n_azar": len(azar)}

    sl, so = j["desp2_solo_lean"], j["desp2_sonda"]
    out = {"base": [float(auc[0]), *ic(rW[:, 0])], "placebo": float(auc[j["placebo"]]),
           "f2": fam("desp2_sonda", "desp2"), "f4": fam("desp4_sonda", "desp4"), "f8": fam("desp8_sonda", "desp8"),
           "pareja": fam("pareja_sonda", "pareja"), "borrar": fam("borrar_sonda", "borrar"),
           "solo_lean_f2_auroc": float(auc[sl]), "solo_lean_f2_caida": float(caida[sl]),
           "sonda_menos_solo_lean_f2": [float(caida[so] - caida[sl]), *ic(rW[:, sl] - rW[:, so])]}
    # coincide con lo que escribió intercambio.py, a cuatro decimales
    g4 = json.load(open(os.path.join(salida, "s5.json"), encoding="utf-8"))
    r4 = lambda v: [round(x, 4) for x in v] if isinstance(v, list) else round(v, 4)
    pares_a_cotejar = [(out["base"][0], g4["base"]["auroc"]), (out["f2"]["auroc"], g4["principal_desplazar_f2"]["auroc"]),
                       (out["f2"]["caida"], g4["principal_desplazar_f2"]["caida"]),
                       (out["f2"]["menos_azar"], g4["principal_desplazar_f2"]["caida_menos_media_azar"]),
                       (out["f2"]["azar_max"], g4["principal_desplazar_f2"]["caida_azar_max"]),
                       (out["f8"]["auroc"], g4["dosis_f8"]["auroc"]), (out["pareja"]["menos_azar"], g4["pareja"]["caida_menos_media_azar"]),
                       (out["borrar"]["menos_azar"], g4["borrar"]["caida_menos_media_azar"]),
                       (out["sonda_menos_solo_lean_f2"], g4["control_solo_lean"]["caida_sonda_menos_solo_lean_f2"])]
    for mio, suyo in pares_a_cotejar:
        assert r4(mio) == suyo, (nombre, r4(mio), suyo)
    assert out["f2"]["supera_a_todas"] == g4["principal_desplazar_f2"]["mayor_que_todas_las_de_azar"]
    out["criterio"] = bool(g4["criterio_principal_cumplido"])
    return out


def s3(nombre):
    d = json.load(open(os.path.join(S.PROBES, "sin_pregunta", "resultados", f"s3_{nombre}.json"), encoding="utf-8"))
    return {b: {"n_pares": d[b]["n_pares"], "auroc": d[b]["auroc"], "media_menos": d[b]["full_media_menos"],
                "ultimo_menos": d[b]["full_ultimo_menos"]} for b in ("principal", "sin_C2")}


def f3(x, signo=False):
    t = f"{abs(x):.3f}"
    neg = x < 0 and float(t) != 0
    return (MENOS if neg else ("+" if signo else "")) + t


def tri(t):                      # +0.216 [+0.166, +0.266], como en las tablas del artículo
    return f"{f3(t[0], True)} [{f3(t[1], True)}, {f3(t[2], True)}]"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--latex", action="store_true")
    a = ap.parse_args()
    T = {"s5": {m: s5_sin_redondear(m) for m, _ in MODELOS}, "s3": {m: s3(m) for m, _ in MODELOS}}
    ruta = os.path.join(AQUI, "resultados_s5", "tablas_nivel_b.json")
    json.dump(T, open(ruta, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print("S5 coincide con s5.json a cuatro decimales en los cuatro modelos. Escrito:", os.path.relpath(ruta, os.path.dirname(S.PROBES)))
    print("\n== S3, segunda lectura: full (media sobre Lean) menos cada control, 377 pares")
    for m, n in MODELOS:
        p = T["s3"][m]["principal"]
        print(f"{n:13s}& {f3(p['auroc']['full_media'][0])} & " + " & ".join(tri(p["media_menos"][k]) for k in ("ngramas", "cruzada", "p_yes", "combinada")) + r"\\")
    p = T["s3"]["qwen3_4b"]["principal"]["auroc"]
    print("   controles solos: n-gramas", f3(p["ngramas"][0]), "| cruzada", f3(p["cruzada"][0]), "| combinada", f3(p["combinada"][0]))
    print("   P(Yes) por modelo:", ", ".join(f"{n} {f3(T['s3'][m]['principal']['auroc']['p_yes'][0])}" for m, n in MODELOS))
    print("\n== S3, último token: full menos el control combinado")
    for m, n in MODELOS:
        print(f"{n:13s}  {tri(T['s3'][m]['principal']['ultimo_menos']['combinada'])}")
    print("\n== S3 sin C2 (309 pares), segunda lectura")
    for m, n in MODELOS:
        p = T["s3"][m]["sin_C2"]
        print(f"{n:13s}& {f3(p['auroc']['full_media'][0])} & " + " & ".join(tri(p["media_menos"][k]) for k in ("ngramas", "cruzada", "p_yes", "combinada")) + r"\\")
    print("\n== S5, f = 2: base & f=2 & caída & azar media; máx & caída − media al azar & iguales o mayores de 20 & criterio")
    for m, n in MODELOS:
        d = T["s5"][m]; p = d["f2"]
        print(f"{n:13s}& {f3(d['base'][0])} & {f3(p['auroc'])} & {tri(p['caida'])} & {f3(p['azar_media'], True)}; {f3(p['azar_max'], True)} & "
              f"{tri(p['menos_azar'])} & {p['n_azar_iguales_o_mayores']} & {'sí' if d['criterio'] else 'no'}" + r"\\")
    print("\n== S5, secundarias: AUROC f=4 & f=8 & pareja − azar & borrar − azar & sonda − lean_only (f=2) & placebo")
    for m, n in MODELOS:
        d = T["s5"][m]
        print(f"{n:13s}& {f3(d['f4']['auroc'])} & {f3(d['f8']['auroc'])} & {tri(d['pareja']['menos_azar'])} & {tri(d['borrar']['menos_azar'])} & "
              f"{tri(d['sonda_menos_solo_lean_f2'])} & {f3(d['placebo'])}" + r"\\")
    print("   dosis: ¿supera a sus 5 al azar?  " + "; ".join(f"{n}: f4 {'sí' if T['s5'][m]['f4']['supera_a_todas'] else 'no'}, f8 {'sí' if T['s5'][m]['f8']['supera_a_todas'] else 'no'}" for m, n in MODELOS))
    print("   máximo al azar con f=8:", "; ".join(f"{n} {f3(T['s5'][m]['f8']['azar_max'])}" for m, n in MODELOS))


if __name__ == "__main__":
    main()
