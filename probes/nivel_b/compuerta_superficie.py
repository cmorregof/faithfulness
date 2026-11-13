"""Compuerta de superficie del Nivel B (revisor Fable, 2026-11-04). Sin modelos, sin Lean, CPU.

Pregunta: ¿se puede separar la variante fiel de la infiel, dentro de cada par, leyendo SOLO el Lean
de la variante? Si sí, los pares no son mínimos y conviene arreglar el generador antes de gastar GPU.

Medida: regresión logística (C = 1) sobre unigramas y bigramas binarios del Lean variante (sin las
líneas `import`), validación cruzada de 5 pliegues agrupada por ARCHIVO fuente (nunca el mismo
archivo en entrenamiento y prueba), puntajes fuera de muestra; AUROC pareada = media sobre orígenes
de la fracción de pares en que la fiel puntúa más que la infiel (empate = 0,5). Se reporta también
con los operadores de orden enmascarados, por regla fiel, por familia infiel, y la superficie
cruzada NL–Lean (`rasgos_cruzados` de analizar_pares.py), que no es parte de la compuerta.

Descomposición (medida en v2, 4 nov 2026): parte de lo que separa el Lean solo no es la firma de la
regla sino TIPICIDAD: una edición infiel suele producir una forma menos frecuente (`n ≥ 0` en ℕ,
`k > 2` en vez de `3 ≤ k`), y eso se aprende sin NL. Para distinguirlo se calcula una línea base
NO supervisada: puntaje = −(bigramas de tokens de la variante que no aparecen en ningún Lean
ORIGINAL del lote), sin etiquetas; su AUROC pareada es la «tipicidad». El exceso = solo_lean −
tipicidad estima la firma de la regla (lo que el generador sí puede y debe eliminar).

Criterio (--criterio): «estricto» (por defecto): pasa si AUROC pareada solo-Lean ≤ --umbral (0,70).
«firma»: pasa si el exceso sobre la tipicidad ≤ --umbral_firma (0,05). Carlos elige cuál rige
antes de aprobar; lanzar.sh usa el estricto salvo que se le pase CRITERIO=firma. Código de salida 0
si pasa, 3 si no.

Uso:
  (antes de certificar, sobre el emparejamiento provisional)
  biblioteca/.venv/bin/python -I probes/nivel_b/compuerta_superficie.py --candidatos probes/nivel_b/candidatos_v2.jsonl
  (después de certificar, sobre los pares definitivos; lo llama lanzar.sh)
  ... --candidatos probes/nivel_b/candidatos_v2.jsonl --indice probes/nivel_b/datos/pares_indice.jsonl
"""
import argparse
import collections
import importlib.util
import json
import os
import re
import sys

import numpy as np
from sklearn.feature_extraction.text import CountVectorizer
from sklearn.linear_model import LogisticRegression
from sklearn.model_selection import GroupKFold
from sklearn.preprocessing import StandardScaler

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import generar as G  # noqa: E402

TOKEN_LEAN = r"[A-Za-z_][A-Za-z0-9_'.]*|\d+|[^\sA-Za-z0-9_]"
UMBRAL = 0.70


def sin_import(s):
    return "\n".join(l for l in s.splitlines() if not l.startswith("import"))


def auroc_pareada(s, grupos_par):
    """s: puntajes en orden [infiel_0, fiel_0, infiel_1, fiel_1, …]."""
    w = np.array([1.0 if s[2 * k + 1] > s[2 * k] else (0.5 if s[2 * k + 1] == s[2 * k] else 0.0)
                  for k in range(len(s) // 2)])
    ug, inv = np.unique(grupos_par, return_inverse=True)
    return float((np.bincount(inv, weights=w) / np.bincount(inv)).mean())


def oof(textos_o_rasgos, y, g, rasgos=False):
    s = np.zeros(len(y))
    for tr, te in GroupKFold(5).split(y, y, g):
        if rasgos:
            F = textos_o_rasgos
            esc = StandardScaler().fit(F[tr])
            m = LogisticRegression(C=1.0, max_iter=5000).fit(esc.transform(F[tr]), y[tr])
            s[te] = m.predict_proba(esc.transform(F[te]))[:, 1]
        else:
            T = textos_o_rasgos
            v = CountVectorizer(binary=True, ngram_range=(1, 2), min_df=2, token_pattern=TOKEN_LEAN,
                                lowercase=False).fit([T[i] for i in tr])
            m = LogisticRegression(C=1.0, max_iter=5000).fit(v.transform([T[i] for i in tr]), y[tr])
            s[te] = m.predict_proba(v.transform([T[i] for i in te]))[:, 1]
    return s


def bigramas(texto):
    t = re.findall(TOKEN_LEAN, texto)
    return set(zip(t, t[1:]))


def tipicidad(textos, originales):
    """Puntajes no supervisados de tipicidad respecto al corpus de ORIGINALES (sin etiquetas):
    (a) −(bigramas de la variante ausentes de todos los originales);
    (b) log-frecuencia del bigrama MÁS RARO de la variante (frecuencia de documento en los originales);
    (c) media de la log-frecuencia de documento de sus bigramas.
    Devuelve dict nombre -> vector."""
    cuenta = collections.Counter()
    for o in originales:
        cuenta.update(bigramas(sin_import(o)))
    out = {"bigramas_nuevos": [], "bigrama_mas_raro": [], "logfrec_media": []}
    for t in textos:
        bg = bigramas(t)
        lf = [np.log1p(cuenta.get(b, 0)) for b in bg] or [0.0]
        out["bigramas_nuevos"].append(-float(sum(cuenta.get(b, 0) == 0 for b in bg)))
        out["bigrama_mas_raro"].append(float(min(lf)))
        out["logfrec_media"].append(float(np.mean(lf)))
    return {k: np.array(v) for k, v in out.items()}


def medir(filas, umbral=UMBRAL, umbral_firma=0.05, originales=None):
    """filas: lista de (infiel, fiel) con dicts que tienen lean_variante, nl, id_origen, archivo, regla, familia.
    originales: Lean originales del lote (sin etiquetas) para la línea base de tipicidad."""
    pares = filas
    rows = [c for par in pares for c in par]
    y = np.array([0, 1] * len(pares))
    g_arch = np.array([c.get("archivo") or G.archivo_de(c["id_origen"]) for c in rows])
    g_orig = np.array([c["id_origen"] for c in rows])
    gp = g_orig[::2]
    textos = [sin_import(c["lean_variante"]) for c in rows]
    out = {"n_pares": len(pares), "n_origenes": int(len(np.unique(gp))), "n_archivos": int(len(np.unique(g_arch))),
           "umbral": umbral, "umbral_firma": umbral_firma}
    s = oof(textos, y, g_arch)
    out["auroc_pareada_solo_lean"] = auroc_pareada(s, gp)
    s_m = oof([re.sub(r"[<>≤≥]", " REL ", t) for t in textos], y, g_arch)
    out["auroc_pareada_solo_lean_operadores_enmascarados"] = auroc_pareada(s_m, gp)
    if originales is None:
        originales = sorted({c["lean_original"] for c in rows})
    tip = {k: auroc_pareada(v, gp) for k, v in tipicidad(textos, originales).items()}
    out["tipicidad_por_medida"] = tip
    # se toma la medida no supervisada que más separa (elección declarada; ninguna usa etiquetas)
    out["auroc_pareada_tipicidad_no_supervisada"] = max(tip.values())
    out["exceso_firma"] = out["auroc_pareada_solo_lean"] - out["auroc_pareada_tipicidad_no_supervisada"]
    por_fiel, por_fam = {}, {}
    for clave, sel in (("por_regla_fiel", lambda k: pares[k][1]["regla"]),
                       ("por_familia_infiel", lambda k: pares[k][0]["familia"])):
        d = {}
        grupos = collections.defaultdict(list)
        for k in range(len(pares)):
            grupos[sel(k)].append(k)
        for nombre, ks in sorted(grupos.items()):
            if len(ks) >= 20:
                idx = [i for k in ks for i in (2 * k, 2 * k + 1)]
                d[nombre] = {"n_pares": len(ks), "auroc_pareada": auroc_pareada(s[idx], gp[ks])}
            else:
                d[nombre] = {"n_pares": len(ks), "auroc_pareada": None}
        out[clave] = d
    # informativo: superficie cruzada NL–Lean (no decide)
    try:
        spec = importlib.util.spec_from_file_location("analizar_pares", os.path.join(AQUI, "analizar_pares.py"))
        ap = importlib.util.module_from_spec(spec); spec.loader.exec_module(ap)
        F = np.array([ap.rasgos_cruzados(c["nl"], t) for c, t in zip(rows, textos)], float)
        out["auroc_pareada_superficie_cruzada_informativa"] = auroc_pareada(oof(F, y, g_arch, rasgos=True), gp)
    except Exception as e:  # no es parte de la compuerta
        out["auroc_pareada_superficie_cruzada_informativa"] = f"no calculada: {e!r}"
    out["pasa_estricto"] = bool(out["auroc_pareada_solo_lean"] <= umbral)
    out["pasa_firma"] = bool(out["exceso_firma"] <= umbral_firma)
    return out


def pares_desde_candidatos(cands, indice=None):
    idx = {c["id"]: c for c in cands}
    if indice:
        filas = [json.loads(l) for l in open(indice, encoding="utf-8")]
        por_par = collections.defaultdict(dict)
        for r in filas:
            if r["rol"] in ("infiel", "fiel"):
                por_par[r["par"]][r["rol"]] = idx[r["id_candidato"]]
        return [(p["infiel"], p["fiel"]) for _, p in sorted(por_par.items()) if len(p) == 2]
    return [(idx[i], idx[f]) for i, f in G.emparejar(cands)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--candidatos", default=os.path.join(AQUI, "candidatos_v2.jsonl"))
    ap.add_argument("--indice", default=None, help="pares_indice.jsonl de extraer_pares.py (pares certificados)")
    ap.add_argument("--umbral", type=float, default=UMBRAL)
    ap.add_argument("--umbral_firma", type=float, default=0.05)
    ap.add_argument("--criterio", choices=("estricto", "firma"), default="estricto")
    ap.add_argument("--salida", default=None, help="JSON de salida (por defecto junto a --candidatos)")
    a = ap.parse_args()
    cands = [json.loads(l) for l in open(a.candidatos, encoding="utf-8")]
    pares = pares_desde_candidatos(cands, a.indice)
    R = medir(pares, a.umbral, a.umbral_firma, originales=sorted({c["lean_original"] for c in cands}))
    R["criterio"] = a.criterio
    R["pasa"] = R["pasa_estricto"] if a.criterio == "estricto" else R["pasa_firma"]
    R["candidatos"] = os.path.relpath(a.candidatos, G.RAIZ)
    R["indice"] = os.path.relpath(a.indice, G.RAIZ) if a.indice else "(emparejamiento provisional)"
    salida = a.salida or os.path.join(os.path.dirname(a.candidatos),
                                      "compuerta_superficie" + ("_certificados" if a.indice else "_provisional") + ".json")
    json.dump(R, open(salida, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(json.dumps({k: R[k] for k in ("n_pares", "n_origenes", "n_archivos", "auroc_pareada_solo_lean",
                                        "auroc_pareada_solo_lean_operadores_enmascarados",
                                        "auroc_pareada_tipicidad_no_supervisada", "exceso_firma",
                                        "auroc_pareada_superficie_cruzada_informativa",
                                        "pasa_estricto", "pasa_firma", "criterio", "pasa")}, ensure_ascii=False, indent=1))
    print("por regla fiel:", {k: v["auroc_pareada"] for k, v in R["por_regla_fiel"].items()})
    print("por familia infiel:", {k: v["auroc_pareada"] for k, v in R["por_familia_infiel"].items()})
    print("escrito:", os.path.relpath(salida, G.RAIZ))
    if not R["pasa"]:
        print(f"NO PASA ({a.criterio}): solo-Lean {R['auroc_pareada_solo_lean']:.3f}, "
              f"tipicidad {R['auroc_pareada_tipicidad_no_supervisada']:.3f}, exceso {R['exceso_firma']:.3f}")
        sys.exit(3)


if __name__ == "__main__":
    main()
