"""S7. Holm en la prueba central del Nivel B, e intervención de S5 sin los pares C2 (13 nov 2026).

No corre ningún modelo. Sigue probes/intervencion/regla_S7_holm_sin_C2.md.
  Parte A: ajuste de Holm sobre los cuatro valores p de la diferencia en el último token (nivel_b_*_principal.json).
  Parte B: la medida y el criterio de S5 sobre los pyes.npy guardados, restringidos a los pares cuyo miembro
           inadecuado tiene una regla que no empieza por «C2». Descriptivo: lo mismo en los pares C2, la dirección
           de «completo» frente a la de «solo_lean», y las dosis f = 4 y f = 8.
Escribe probes/intervencion/resultados_s5/s7_sin_c2.json.

Uso (desde la raíz de Proyecto Godel; PY=biblioteca/.venv/bin/python):
  $PY -I probes/intervencion/s7_sin_c2.py --prueba      datos sintéticos; comprueba el cálculo. No mira nada real.
  $PY -I probes/intervencion/s7_sin_c2.py --comprobar   cuenta los pares de cada subconjunto en el índice. No lee ningún pyes.npy.
  $PY -I probes/intervencion/s7_sin_c2.py               el análisis. Exige APROBADO_regla_S7 con el SHA-256 de la regla.
"""
import argparse
import hashlib
import json
import os
import sys

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
PROBES = os.path.dirname(AQUI)
sys.path.insert(0, AQUI)
sys.path.insert(0, os.path.join(PROBES, "nivel_b"))
sys.path.insert(0, os.path.join(PROBES, "referencia"))
REGLA = os.path.join(AQUI, "regla_S7_holm_sin_C2.md")
MARCA = os.path.join(AQUI, "APROBADO_regla_S7")
MODELOS = [("qwen3_4b", "Qwen3-4B"), ("olmo2_7b", "OLMo-2-7B"), ("llama31_8b", "Llama-3.1-8B"), ("gemma3_4b", "Gemma-3-4B")]
N_BOOT = 2000


def exigir_marca():
    if not os.path.exists(MARCA):
        sys.exit("Falta probes/intervencion/APROBADO_regla_S7 (la crea Carlos). Sin ella solo corren --prueba y --comprobar.")
    if hashlib.sha256(open(REGLA, "rb").read()).hexdigest() not in open(MARCA, encoding="utf-8").read():
        sys.exit("APROBADO_regla_S7 no contiene el SHA-256 de regla_S7_holm_sin_C2.md: la regla cambió después de aprobarse.")


# ---------------------------------------------------------------- parte A

def holm(ps):
    """Ajuste descendente de Holm, con monotonía forzada y tope en 1. Devuelve los ajustados en el orden de entrada."""
    ps = np.asarray(ps, float)
    orden = np.argsort(ps, kind="stable")
    m = len(ps)
    aj = np.minimum(1.0, np.maximum.accumulate((m - np.arange(m)) * ps[orden]))
    out = np.empty(m)
    out[orden] = aj
    return out.tolist()


def parte_a():
    ps = [json.load(open(os.path.join(PROBES, "nivel_b", "resultados", f"nivel_b_{m}_principal.json"), encoding="utf-8"))
          ["permutaciones"]["diferencia"]["p"] for m, _ in MODELOS]
    aj = holm(ps)
    return {"familia": "p de permutación de la diferencia en el último token, cuatro modelos",
            "p": dict(zip([m for m, _ in MODELOS], ps)), "p_holm": dict(zip([m for m, _ in MODELOS], aj)),
            "n_bajo_0.05": int(sum(x < 0.05 for x in aj))}


# ---------------------------------------------------------------- parte B

def indice_pares(nombre):
    """pares (infiel, fiel), origen de cada par y máscara de los pares C2, sin leer ningún pyes.npy."""
    import ablacion as A
    import intercambio as S
    carpeta, indice, salida = S.rutas(nombre)
    tren, sel, y, g, pares, gp = A.cargar_pares(carpeta, indice)
    c2 = np.array([tren[i]["regla"].startswith("C2") for i in pares[:, 0]])
    return pares, gp, c2, len(y), salida


def cargar(nombre):
    import intercambio as S
    pares, gp, c2, n, salida = indice_pares(nombre)
    nombres = [c[0] for c in S.condiciones()]
    P = np.load(os.path.join(salida, "pyes.npy"))
    assert P.shape == (len(nombres), n, 4), (P.shape, len(nombres), n)
    assert np.load(os.path.join(salida, "hecho.npy")).all() and np.isfinite(P).all()
    return P, nombres, pares, gp, c2


def por_origen(v, gp):
    _, inv = np.unique(gp, return_inverse=True)
    return np.bincount(inv, weights=v) / np.bincount(inv)


def w_pares(s, pares):
    i, f = pares[:, 0], pares[:, 1]
    return np.where(s[f] > s[i], 1.0, np.where(s[f] == s[i], 0.5, 0.0))


def bloque(P, nombres, pares, gp):
    """La medida de S5 (intercambio.paso_analizar) sobre los pares dados."""
    S = P[:, :, 0] / np.maximum(P[:, :, 0] + P[:, :, 1], 1e-12)                 # P(Yes) normalizado
    W = np.array([por_origen(w_pares(s, pares), gp) for s in S])                # (condición, origen)
    auc = W.mean(1)
    m = W.shape[1]
    idx = np.random.default_rng(0).integers(0, m, (N_BOOT, m))
    rW = np.array([W[:, ix].mean(1) for ix in idx])                             # (réplica, condición)
    ic = lambda v: [float(x) for x in np.percentile(v, [2.5, 97.5])]
    j = {n: k for k, n in enumerate(nombres)}
    caida = auc[j["base"]] - auc

    def fam(f):
        so = j[f"desp{f}_sonda"]
        az = [j[n] for n in nombres if n.startswith(f"desp{f}_azar")]
        return {"auroc": float(auc[so]), "auroc_ic": ic(rW[:, so]),
                "caida": [float(caida[so]), *ic(rW[:, j["base"]] - rW[:, so])],
                "azar_media": float(caida[az].mean()), "azar_max": float(caida[az].max()),
                "menos_azar": [float(caida[so] - caida[az].mean()), *ic(rW[:, az].mean(1) - rW[:, so])],
                "n_azar_iguales_o_mayores": int((caida[az] >= caida[so]).sum()), "n_azar": len(az),
                "supera_a_todas": bool((caida[so] > caida[az]).all())}

    so, sl = j["desp2_sonda"], j["desp2_solo_lean"]
    out = {"n_pares": int(len(pares)), "n_origenes": int(m),
           "base": [float(auc[j["base"]]), *ic(rW[:, j["base"]])], "placebo": float(auc[j["placebo"]]),
           "f2": fam(2), "f4": fam(4), "f8": fam(8),
           "sonda_menos_solo_lean_f2": [float(caida[so] - caida[sl]), *ic(rW[:, sl] - rW[:, so])]}
    return out


def lectura(b):
    """Regla S7, B4. Devuelve (lectura, sin_senal_de_partida)."""
    sin_senal = b["base"][1] <= 0.5 <= b["base"][2]
    p = b["f2"]
    cumple = p["menos_azar"][1] > 0 and p["supera_a_todas"]
    return ("cumple sin C2" if cumple else "no cumple sin C2"), bool(sin_senal)


def analizar(P, nombres, pares, gp, c2):
    sin = bloque(P, nombres, pares[~c2], gp[~c2])
    sin["lectura"], sin["sin_senal_de_partida"] = lectura(sin)
    return {"sin_C2": sin, "C2_descriptivo": bloque(P, nombres, pares[c2], gp[c2])}


# ---------------------------------------------------------------- pruebas y principal

def prueba():
    """Datos sintéticos con la forma de S5 y respuesta conocida."""
    import intercambio as S
    assert np.allclose(holm([0.0099, 0.0198, 0.0198, 0.0594]), [0.0396, 0.0594, 0.0594, 0.0594])
    assert np.allclose(holm([0.5, 0.01, 0.9]), [1.0, 0.03, 1.0])
    nombres = [c[0] for c in S.condiciones()]
    rng = np.random.default_rng(1)
    n_par = 120
    pares = np.arange(2 * n_par).reshape(n_par, 2)                               # (infiel, fiel)
    gp = np.repeat(np.arange(n_par // 2), 2)
    c2 = np.arange(n_par) % 4 == 0
    y = np.tile([0, 1], n_par)
    for caso, efecto_fuera, espera in (("el efecto solo está en C2", False, "no cumple sin C2"),
                                       ("el efecto está en todos los pares", True, "cumple sin C2")):
        P = np.zeros((len(nombres), 2 * n_par, 4))
        for k, n in enumerate(nombres):
            senal = 1.5 * y + rng.standard_normal(2 * n_par)                     # la fiel puntúa más
            if n == "desp2_sonda":
                fila_c2 = np.repeat(c2, 2)
                quita = fila_c2 | efecto_fuera
                senal = np.where(quita, rng.standard_normal(2 * n_par), senal)   # el desplazamiento borra la señal
            p = 1 / (1 + np.exp(-senal))
            P[k, :, 0], P[k, :, 1] = 0.9 * p, 0.9 * (1 - p)
        r = analizar(P, nombres, pares, gp, c2)["sin_C2"]
        print(f"{caso}: caída menos azar = {r['f2']['menos_azar'][0]:+.3f} -> {r['lectura']}")
        assert r["lectura"] == espera and r["n_pares"] == int((~c2).sum()) and not r["sin_senal_de_partida"]
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
            pares, gp, c2, filas, _ = indice_pares(m)
            print(f"{n:13s} {len(pares)} pares, {filas} filas; sin C2: {int((~c2).sum())} pares en "
                  f"{len(np.unique(gp[~c2]))} orígenes; C2: {int(c2.sum())} pares en {len(np.unique(gp[c2]))} orígenes")
        return
    exigir_marca()
    # cordura: con los 377 pares, esta implementación debe reproducir las cifras de S5 ya publicadas
    S5 = json.load(open(os.path.join(AQUI, "resultados_s5", "tablas_nivel_b.json"), encoding="utf-8"))["s5"]
    for m, _ in MODELOS:
        P, nombres, pares, gp, c2 = cargar(m)
        t = bloque(P, nombres, pares, gp)
        for a_, b_ in ((t["base"][0], S5[m]["base"][0]), (t["f2"]["auroc"], S5[m]["f2"]["auroc"]),
                       (t["f2"]["menos_azar"][0], S5[m]["f2"]["menos_azar"][0]),
                       (t["f2"]["menos_azar"][1], S5[m]["f2"]["menos_azar"][1])):
            assert abs(a_ - b_) < 1e-6, (m, a_, b_)
    T = {"regla_sha256": hashlib.sha256(open(REGLA, "rb").read()).hexdigest(), "holm": parte_a(),
         "sin_C2": {m: analizar(*cargar(m)) for m, _ in MODELOS}}
    ruta = os.path.join(AQUI, "resultados_s5", "s7_sin_c2.json")
    json.dump(T, open(ruta, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    f3 = lambda x: f"{x:.3f}"
    s3 = lambda t: f"{t[0]:+.3f} [{t[1]:+.3f}, {t[2]:+.3f}]"
    h = T["holm"]
    print("Parte A. Holm sobre los cuatro p de la diferencia:")
    for m, n in MODELOS:
        print(f"  {n:13s} p = {h['p'][m]:.4f}   ajustado = {h['p_holm'][m]:.3f}")
    print(f"  por debajo de 0.05 tras el ajuste: {h['n_bajo_0.05']} de 4")
    for clave, titulo in (("sin_C2", "Parte B. Sin C2"), ("C2_descriptivo", "Descriptivo. Solo C2")):
        print(f"\n{titulo}: pares | base [IC] | desplazada | caída menos media al azar [IC] | azar ≥ sonda | full − lean_only | ×2, ×4"
              + (" | lectura" if clave == "sin_C2" else ""))
        for m, n in MODELOS:
            d = T["sin_C2"][m][clave]; p = d["f2"]
            fila = (f"  {n:13s} {d['n_pares']} | {f3(d['base'][0])} [{f3(d['base'][1])}, {f3(d['base'][2])}] | {f3(p['auroc'])} | "
                    f"{s3(p['menos_azar'])} | {p['n_azar_iguales_o_mayores']} de {p['n_azar']} | {s3(d['sonda_menos_solo_lean_f2'])} | "
                    f"{f3(d['f4']['auroc'])}, {f3(d['f8']['auroc'])}")
            if clave == "sin_C2":
                fila += f" | {d['lectura']}" + (" (sin señal de partida)" if d["sin_senal_de_partida"] else "")
            print(fila)
    print("\nEscrito:", os.path.relpath(ruta, os.path.dirname(PROBES)))


if __name__ == "__main__":
    main()
