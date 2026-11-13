"""Réplica de S5 en Gemma-3, OLMo-2 y Llama-3.1 (12 nov 2026).

Envuelve probes/intervencion/intercambio.py SIN modificarlo: mismas 54 condiciones, mismas semillas, mismo
análisis y mismo criterio que en Qwen3-4B. Lo único que cambia es el modelo y la regla que autoriza la corrida:
probes/intervencion/regla_S5_replica.md, con su marca probes/intervencion/APROBADO_regla_S5_replica (la crea
Carlos). Ningún paso corre sin la marca, tampoco «direcciones» ni el humo.

Pasos, por modelo:
  direcciones   CPU
  humo          4 pares y 9 condiciones; además de los ganchos, exige que el prompt y la máscara reproduzcan la
                extracción guardada (coordenada limpia frente a guardada y P(Yes) de base frente al guardado)
  correr        754 filas, 54 condiciones (se puede cortar y reanudar)
  analizar      escribe resultados_s5/<modelo>/s5.json
y al final:
  resumen       tabla de los tres modelos y la frase que fija la regla

Uso (desde la raíz de Proyecto Godel; PY=biblioteca/.venv/bin/python):
  HF_HUB_OFFLINE=1 $PY -I probes/intervencion/replica_s5.py --paso humo --nombre gemma3_4b
  $PY -I probes/intervencion/replica_s5.py --paso resumen
Lo normal es lanzar probes/intervencion/replica_s5.sh, que encadena todo.
"""
import argparse
import hashlib
import json
import os
import sys
import types

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import intercambio as S  # noqa: E402

MODELOS = ("gemma3_4b", "olmo2_7b", "llama31_8b")
NOMBRE = {"gemma3_4b": "Gemma-3", "olmo2_7b": "OLMo-2", "llama31_8b": "Llama-3.1"}
SHA_GUION_S5 = "8c948cd81e344b83bc198b7bb80a16b16ca31b0ebee5a25fd431028c36595e23"   # intercambio.py de la noche del 11 nov
MARCA = os.path.join(AQUI, "APROBADO_regla_S5_replica")
REGLA = os.path.join(AQUI, "regla_S5_replica.md")
S.MARCA, S.REGLA = MARCA, REGLA                 # intercambio.py comprobará esta marca, no la de S5
UMBRAL_VIVA, UMBRAL_BASE = 0.05, 0.2            # fijados en la regla


def sha(ruta):
    return hashlib.sha256(open(ruta, "rb").read()).hexdigest()


def exigir():
    if not os.path.exists(REGLA):
        sys.exit("Falta probes/intervencion/regla_S5_replica.md.")
    if not os.path.exists(MARCA):
        sys.exit("Falta probes/intervencion/APROBADO_regla_S5_replica (la crea Carlos). Sin ella no corre ningún paso.")
    if sha(REGLA) not in open(MARCA, encoding="utf-8").read():
        sys.exit("regla_S5_replica.md cambió después de aprobarse (su SHA-256 no está en la marca). No corro.")


def guion():
    h = sha(os.path.join(AQUI, "intercambio.py"))
    if h != SHA_GUION_S5:
        print(f"AVISO: intercambio.py no es el de la noche del 11 nov (SHA-256 {h[:12]}…). "
              "La regla solo admite arreglos de compatibilidad, y hay que anotarlos.", flush=True)
    return h


def args_s5(nombre, lote, prueba=None, forzar=False):
    return types.SimpleNamespace(nombre=nombre, lote=lote, prueba=prueba, forzar=forzar, sintetico=False)


def revisar_humo(c):
    """Devuelve la lista de problemas del humo (vacía si pasa)."""
    mal = []
    viva = (c.get("coordenada_viva_vs_guardada_capa_fija_en_h") or {}).get("mediana")
    base = c.get("base_vs_pyes_guardado_max_abs")
    if viva is None or not viva <= UMBRAL_VIVA:
        mal.append(f"la coordenada limpia no reproduce la guardada (mediana {viva} h; umbral {UMBRAL_VIVA})")
    if base is None or not base <= UMBRAL_BASE:
        mal.append(f"el P(Yes) de base no reproduce el guardado (diferencia máxima {base}; umbral {UMBRAL_BASE})")
    return mal


def paso_humo(a):
    S.paso_correr(args_s5(a.nombre, a.lote, prueba=4, forzar=a.forzar))
    c = json.load(open(os.path.join(S.rutas(a.nombre)[2] + "_prueba4", "corrida.json"), encoding="utf-8"))
    mal = revisar_humo(c)
    if mal:
        sys.exit(f"Humo de {a.nombre}: NO pasa. " + "; ".join(mal) + ". No corro este modelo.")
    print(f"Humo de {a.nombre}: pasa (ganchos, coordenada limpia y P(Yes) de base).", flush=True)


def paso_resumen(a):
    filas, cumplen, sin_evaluar = [], [], []
    for m in MODELOS:
        ruta = os.path.join(S.rutas(m)[2], "s5.json")
        if not os.path.exists(ruta):
            sin_evaluar.append(m)
            continue
        d = json.load(open(ruta, encoding="utf-8"))
        p = d["principal_desplazar_f2"]
        if d["criterio_principal_cumplido"]:
            cumplen.append(m)
        filas.append({"modelo": m, "auroc_base": d["base"]["auroc"], "auroc_placebo": d["placebo"]["auroc"],
                      "auroc_f2": p["auroc"], "caida_f2": p["caida"], "caida_azar_media": p["caida_azar_media"],
                      "caida_azar_max": p["caida_azar_max"], "caida_menos_media_azar": p["caida_menos_media_azar"],
                      "mayor_que_todas_las_de_azar": p["mayor_que_todas_las_de_azar"],
                      "margen_firmado_menos_media_azar": p["margen_firmado_menos_media_azar"],
                      "auroc_f4": d["dosis_f4"]["auroc"], "auroc_f8": d["dosis_f8"]["auroc"],
                      "caida_pareja": d["pareja"]["caida"], "caida_borrar": d["borrar"]["caida"],
                      "caida_sonda_menos_solo_lean_f2": d["control_solo_lean"]["caida_sonda_menos_solo_lean_f2"],
                      "criterio_principal_cumplido": d["criterio_principal_cumplido"]})
    evaluados = len(filas)
    if evaluados == 0:
        frase = "Ningún modelo de la réplica se ha evaluado todavía."
    else:
        quienes = ", ".join(NOMBRE[m] for m in cumplen) or "ninguno"
        frase = (f"Con el mismo guion y el mismo criterio, fijados antes de correr, el resultado de S5 en Qwen3-4B se repite "
                 f"en {len(cumplen)} de los {evaluados} modelos evaluados ({quienes}).")
        if sin_evaluar:
            frase += " Sin evaluar por fallo técnico o corrida incompleta: " + ", ".join(NOMBRE[m] for m in sin_evaluar) + "."
    out = {"regla_sha256": sha(REGLA) if os.path.exists(REGLA) else None, "guion_sha256": guion(),
           "guion_es_el_de_s5": sha(os.path.join(AQUI, "intercambio.py")) == SHA_GUION_S5,
           "modelos": filas, "cumplen": cumplen, "sin_evaluar": sin_evaluar, "frase": frase}
    json.dump(out, open(os.path.join(AQUI, "resultados_s5", "replica_resumen.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=2)
    f3 = lambda t: f"{t[0]:+.3f} [{t[1]:.3f}; {t[2]:.3f}]"
    print(f"{'modelo':11s} {'base':>6s} {'f=2':>6s} {'caída f=2':>24s} {'azar media; máx':>16s} {'caída − azar':>24s} {'f=4':>6s} {'f=8':>6s}  criterio")
    for r in filas:
        print(f"{r['modelo']:11s} {r['auroc_base']:6.3f} {r['auroc_f2']:6.3f} {f3(r['caida_f2']):>24s} "
              f"{r['caida_azar_media']:7.3f}; {r['caida_azar_max']:6.3f} {f3(r['caida_menos_media_azar']):>24s} "
              f"{r['auroc_f4']:6.3f} {r['auroc_f8']:6.3f}  {'CUMPLE' if r['criterio_principal_cumplido'] else 'no cumple'}")
    for m in sin_evaluar:
        print(f"{m:11s} sin evaluar")
    print("\n" + frase)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paso", required=True, choices=["direcciones", "humo", "correr", "analizar", "resumen"])
    ap.add_argument("--nombre", choices=MODELOS)
    ap.add_argument("--lote", type=int, default=4)
    ap.add_argument("--forzar", action="store_true")
    a = ap.parse_args()
    exigir()
    if a.paso == "resumen":
        return paso_resumen(a)
    if not a.nombre:
        sys.exit("Falta --nombre (gemma3_4b, olmo2_7b o llama31_8b).")
    guion()
    if a.paso == "humo":
        return paso_humo(a)
    {"direcciones": S.paso_direcciones, "correr": S.paso_correr, "analizar": S.paso_analizar}[a.paso](
        args_s5(a.nombre, a.lote, forzar=a.forzar))


if __name__ == "__main__":
    main()
