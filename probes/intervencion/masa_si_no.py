"""S6. Masa de probabilidad en « Yes» y « No» bajo la intervención de S5 (13 nov 2026).

No corre ningún modelo. Lee los pyes.npy de S5 y mide M = P(Yes) + P(No) por condición, como fija
probes/intervencion/regla_S6_masa.md. Escribe probes/intervencion/resultados_s5/s6_masa.json.

Uso (desde la raíz de Proyecto Godel; PY=biblioteca/.venv/bin/python):
  $PY -I probes/intervencion/masa_si_no.py --prueba      datos sintéticos; comprueba el cálculo. No mira nada real.
  $PY -I probes/intervencion/masa_si_no.py --comprobar   carga los cuatro modelos y revisa formas. No imprime valores.
  $PY -I probes/intervencion/masa_si_no.py               el análisis. Exige APROBADO_regla_S6 con el SHA-256 de la regla.
"""
import argparse
import hashlib
import json
import os
import sys

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
REGLA = os.path.join(AQUI, "regla_S6_masa.md")
MARCA = os.path.join(AQUI, "APROBADO_regla_S6")
MODELOS = [("qwen3_4b", "Qwen3-4B"), ("olmo2_7b", "OLMo-2-7B"), ("llama31_8b", "Llama-3.1-8B"), ("gemma3_4b", "Gemma-3-4B")]
N_BOOT = 2000


def exigir_marca():
    if not os.path.exists(MARCA):
        sys.exit("Falta probes/intervencion/APROBADO_regla_S6 (la crea Carlos). Sin ella solo corren --prueba y --comprobar.")
    if hashlib.sha256(open(REGLA, "rb").read()).hexdigest() not in open(MARCA, encoding="utf-8").read():
        sys.exit("APROBADO_regla_S6 no contiene el SHA-256 de regla_S6_masa.md: la regla cambió después de aprobarse.")


def cargar(nombre):
    import ablacion as A
    import intercambio as S
    carpeta, indice, salida = S.rutas(nombre)
    tren, sel, y, g, pares, gp = A.cargar_pares(carpeta, indice)
    nombres = [c[0] for c in S.condiciones()]
    P = np.load(os.path.join(salida, "pyes.npy"))
    assert P.shape == (len(nombres), len(y), 4), (P.shape, len(nombres), len(y))
    assert np.load(os.path.join(salida, "hecho.npy")).all() and np.isfinite(P).all()
    return P, nombres, pares, gp


def por_origen(v, gp):
    _, inv = np.unique(gp, return_inverse=True)
    return np.bincount(inv, weights=v) / np.bincount(inv)


def analizar(P, nombres, pares, gp):
    M = P[:, :, 0] + P[:, :, 1]                                           # (condición, fila)
    W = np.array([por_origen((m[pares[:, 0]] + m[pares[:, 1]]) / 2, gp) for m in M])   # (condición, origen)
    med = W.mean(1)
    m = W.shape[1]
    idx = np.random.default_rng(0).integers(0, m, (N_BOOT, m))
    rW = np.array([W[:, ix].mean(1) for ix in idx])                       # (réplica, condición)
    ic = lambda v: [float(x) for x in np.percentile(v, [2.5, 97.5])]
    j = {n: k for k, n in enumerate(nombres)}

    def fam(f):
        so = j[f"desp{f}_sonda"]
        az = [j[n] for n in nombres if n.startswith(f"desp{f}_azar")]
        D = [float(med[so] - med[az].mean()), *ic(rW[:, so] - rW[:, az].mean(1))]
        return {"sonda": [float(med[so]), *ic(rW[:, so])], "azar_media": float(med[az].mean()),
                "azar_min": float(med[az].min()), "azar_max": float(med[az].max()), "n_azar": len(az),
                "sonda_menos_media_azar": D, "n_azar_con_masa_igual_o_menor": int((med[az] <= med[so]).sum()),
                "menor_que_todas_las_de_azar": bool((med[so] < med[az]).all())}

    out = {"base": [float(med[j["base"]]), *ic(rW[:, j["base"]])], "placebo": float(med[j["placebo"]]),
           "f2": fam(2), "f4": fam(4), "f8": fam(8)}
    p = out["f2"]
    pierde = p["sonda_menos_media_azar"][2] < 0 and p["menor_que_todas_las_de_azar"]
    out["lectura"] = "pierde más masa que el azar" if pierde else "no se establece que pierda más masa que el azar"
    return out


def prueba():
    """Datos sintéticos con la forma de S5. Dos casos con respuesta conocida."""
    import intercambio as S
    nombres = [c[0] for c in S.condiciones()]
    rng = np.random.default_rng(1)
    n_par = 60
    pares = np.arange(2 * n_par).reshape(n_par, 2)
    gp = np.repeat(np.arange(n_par // 2), 2)
    for caso, baja in (("la sonda conserva la masa", 0.0), ("la sonda pierde masa", 0.4)):
        P = np.zeros((len(nombres), 2 * n_par, 4))
        masa = np.clip(0.9 + 0.02 * rng.standard_normal(P.shape[:2]), 0, 1)
        az = [k for k, n in enumerate(nombres) if n.startswith("desp2_azar")]
        masa[nombres.index("desp2_sonda")] = masa[az].mean(0) - baja     # sin efecto: igual a la media de las de azar
        P[:, :, 0], P[:, :, 1] = masa * 0.6, masa * 0.4
        r = analizar(P, nombres, pares, gp)
        print(f"{caso}: D = {r['f2']['sonda_menos_media_azar'][0]:+.3f} -> {r['lectura']}")
        assert (r["lectura"] == "pierde más masa que el azar") == (baja > 0)
    print("prueba sintética correcta;", len(nombres), "condiciones")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prueba", action="store_true")
    ap.add_argument("--comprobar", action="store_true")
    a = ap.parse_args()
    if a.prueba:
        return prueba()
    if a.comprobar:
        for m, n in MODELOS:
            P, nombres, pares, gp = cargar(m)
            print(f"{n:13s} pyes {P.shape}, {len(pares)} pares, {len(np.unique(gp))} orígenes: carga correcta")
        return
    exigir_marca()
    T = {m: analizar(*cargar(m)) for m, _ in MODELOS}
    ruta = os.path.join(AQUI, "resultados_s5", "s6_masa.json")
    json.dump(T, open(ruta, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    f3 = lambda x: f"{x:.3f}"
    print("S6, f = 2: base | placebo | sonda [IC] | azar media (mín a máx) | sonda − media azar [IC] | azar con masa igual o menor | lectura")
    for m, n in MODELOS:
        d = T[m]; p = d["f2"]; D = p["sonda_menos_media_azar"]
        print(f"{n:13s} {f3(d['base'][0])} | {f3(d['placebo'])} | {f3(p['sonda'][0])} [{f3(p['sonda'][1])}, {f3(p['sonda'][2])}] | "
              f"{f3(p['azar_media'])} ({f3(p['azar_min'])} a {f3(p['azar_max'])}) | {D[0]:+.3f} [{D[1]:+.3f}, {D[2]:+.3f}] | "
              f"{p['n_azar_con_masa_igual_o_menor']} de {p['n_azar']} | {d['lectura']}")
    print("Escrito:", os.path.relpath(ruta, os.path.dirname(os.path.dirname(AQUI))))


if __name__ == "__main__":
    main()
