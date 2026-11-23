"""Arma las tablas del informe a partir de los comparacion.json. No calcula nada nuevo.

  python tablas_informe.py > tablas_informe.md
"""
import json, sys
from pathlib import Path

import numpy as np

AQUI = Path(__file__).resolve().parent
MENOS = "−"
NIVEL_A = [("qwen3_4b", "Qwen3-4B"), ("olmo2_7b", "OLMo-2-7B"), ("gemma3_4b", "Gemma-3-4B"), ("llama31_8b", "Llama-3.1-8B"),
           ("dsprover2_7b", "DeepSeek-Prover-V2-7B"), ("goedel_8b", "Goedel-Prover-V2-8B"), ("kimina_7b", "Kimina-7B"), ("qwen3_8b", "Qwen3-8B")]
ETIQ = {("nivel_c", "i"): "`ultimo`, capa anidada"}
NIVEL_C = [("qwen3_4b_proofnetverif", "Qwen3-4B"), ("llama31_8b_proofnetverif", "Llama-3.1-8B")]


def s(x, d=4):
    t = f"{abs(x):.{d}f}"
    return (MENOS if x < 0 and float(t) != 0 else "+") + t


def ic(v, signo=False):
    f = (lambda x: s(x)) if signo else (lambda x: f"{x:.4f}")
    return f"{f(v[0])} [{f(v[1])}, {f(v[2])}]"


def tabla_principal(nivel, modelos, lecturas):
    print("| Modelo | Lectura | Cantidad | `probe.py` | Referencia | Diferencia | ¿Dentro de 0.005? | ¿Misma decisión? |")
    print("|---|---|---|---|---|---|---|---|")
    for clave, nombre in modelos:
        ruta = AQUI / "salida" / nivel / clave / "comparacion.json"
        if not ruta.exists():
            print(f"| {nombre} | | sin comparar | | | | | |")
            continue
        c = json.loads(ruta.read_text(encoding="utf-8"))
        for corta in lecturas:
            e = c["lecturas"][corta]
            for cantidad, f in e["cantidades"].items():
                es_delta = cantidad == "Δ"
                decision = ""
                if es_delta:
                    d = e["decision"]
                    decision = ("sí" if e["misma_decision"] else "NO") + f" ({d['probe']} / {d['referencia']})"
                print(f"| {nombre} | {ETIQ.get((nivel, corta), "(" + corta + ")")} | {cantidad} | {ic(f['probe'], es_delta)} | {ic(f['referencia'], es_delta)} | "
                      f"{s(f['diferencia'])} | {'sí' if f['dentro'] else 'NO'} | {decision} |")


def tabla_capas(nivel, modelos):
    print("| Modelo | Capas iguales, completo | Capas iguales, solo_lean | Particiones con capa distinta (semilla, partición: `probe.py` / referencia) |")
    print("|---|---|---|---|")
    for clave, nombre in modelos:
        ruta = AQUI / "salida" / nivel / clave / "comparacion.json"
        if not ruta.exists():
            continue
        k = json.loads(ruta.read_text(encoding="utf-8"))["lecturas"]["i"]["capas"]
        dist = "; ".join(f"{v} s{d['semilla']} p{d['particion'] + 1}: {d['probe']} / {d['referencia']}"
                         for v in ("completo", "solo_lean") for d in k[v]["distintas"]) or "ninguna"
        print(f"| {nombre} | {k['completo']['iguales']} de {k['completo']['de']} | {k['solo_lean']['iguales']} de {k['solo_lean']['de']} | {dist} |")


def tabla_capas_elegidas(nivel, modelos):
    print("| Modelo | Condición | Semilla 0 | Semilla 1 | Semilla 2 | Semilla 3 | Semilla 4 |")
    print("|---|---|---|---|---|---|---|")
    for clave, nombre in modelos:
        ruta = AQUI / "salida" / nivel / clave / "comparacion.json"
        if not ruta.exists():
            continue
        k = json.loads(ruta.read_text(encoding="utf-8"))["lecturas"]["i"]["capas"]
        for v in ("completo", "solo_lean"):
            print(f"| {nombre} | {v} | " + " | ".join(", ".join(str(x) for x in sem) for sem in k[v]["probe"]) + " |")


def tabla_correlacion(nivel, modelos, lecturas):
    print("| Modelo | Lectura | Condición | Pearson | Spearman | Mayor diferencia absoluta | `y` idéntico |")
    print("|---|---|---|---|---|---|---|")
    for clave, nombre in modelos:
        ruta = AQUI / "salida" / nivel / clave / "comparacion.json"
        if not ruta.exists():
            continue
        c = json.loads(ruta.read_text(encoding="utf-8"))
        for corta in lecturas:
            e = c["lecturas"][corta]
            for v, r in e["correlacion_fila_a_fila"].items():
                print(f"| {nombre} | {ETIQ.get((nivel, corta), "(" + corta + ")")} | {v} | {r['pearson']:.4f} | {r['spearman']:.4f} | {r['max_dif_abs']:.3f} | {'sí' if e['y_identico'] else 'NO'} |")


def tabla_barajadas(nivel, modelos):
    print("| Modelo | Capas | Media de la AUROC barajada por capa | Rango de los quince valores |")
    print("|---|---|---|---|")
    for clave, nombre in modelos:
        ruta = AQUI / "salida" / nivel / clave / "barajadas.json"
        if not ruta.exists():
            continue
        b = json.loads(ruta.read_text(encoding="utf-8"))
        print(f"| {nombre} | {', '.join(str(x) for x in b['capas'])} | {', '.join(f'{x:.3f}' for x in b['auroc_media'])} | "
              f"{np.min(b['todas']):.3f} a {np.max(b['todas']):.3f} |")


def tabla_tiempos(nivel, modelos, lecturas):
    print("| Modelo | Forma de las activaciones | " + " | ".join(f"Lectura ({l}), s" for l in lecturas) + " | Barajadas, s | Salidas escritas | Referencia abierta |")
    print("|---|---|" + "---|" * (len(lecturas) + 3))
    for clave, nombre in modelos:
        S = AQUI / "salida" / nivel / clave
        if not (S / "comparacion.json").exists():
            continue
        c = json.loads((S / "comparacion.json").read_text(encoding="utf-8"))
        forma = c["datos"]["formas"]
        forma = forma.get("completo_ultimo", forma.get("completo"))
        seg = []
        for l in lecturas:
            j = json.loads((S / f"lectura_{l}.json").read_text(encoding="utf-8"))
            seg.append(f"{j.get('segundos_cpu_de_las_diez_corridas', j['segundos']):.0f}")
        print(f"| {nombre} | {tuple(forma['forma'])}, {forma['dtype']} | " + " | ".join(seg) +
              f" | {c['barajadas']['segundos']:.0f} | {c['salidas_escritas'][11:19]} | {c['referencia_abierta'][11:19]} |")


if __name__ == "__main__":
    print("## Nivel A\n")
    tabla_principal("nivel_a", NIVEL_A, ("i", "ii"))
    print("\n### Capas de la lectura (i) frente a la referencia\n")
    tabla_capas("nivel_a", NIVEL_A)
    print("\n### Capas elegidas por `probe.py` en la lectura (i), por semilla (cinco particiones externas cada una)\n")
    tabla_capas_elegidas("nivel_a", NIVEL_A)
    print("\n### Correlación fila a fila (450 filas)\n")
    tabla_correlacion("nivel_a", NIVEL_A, ("i", "ii"))
    print("\n### Barajadas\n")
    tabla_barajadas("nivel_a", NIVEL_A)
    print("\n### Tiempos\n")
    tabla_tiempos("nivel_a", NIVEL_A, ("i", "ii"))
    if (AQUI / "salida" / "nivel_c").exists():
        print("\n## Nivel C\n")
        tabla_principal("nivel_c", NIVEL_C, ("i",))
        print("\n### Capas frente a la referencia\n")
        tabla_capas("nivel_c", NIVEL_C)
        print("\n### Capas elegidas por `probe.py`\n")
        tabla_capas_elegidas("nivel_c", NIVEL_C)
        print("\n### Correlación fila a fila (3752 filas)\n")
        tabla_correlacion("nivel_c", NIVEL_C, ("i",))
        print("\n### Barajadas\n")
        tabla_barajadas("nivel_c", NIVEL_C)
        print("\n### Tiempos\n")
        tabla_tiempos("nivel_c", NIVEL_C, ("i",))
