"""Compara las salidas de correr_nivel_c.py con los resultados de la referencia del Nivel C (C1 principal).

Solo lee resultados: nivel_c/resultados/resultados_c_<modelo>.json y puntajes_c_<modelo>.npz, y, si existe,
el resultado de la segunda implementación (nivel_c/segunda_implementacion/resultado_c1.json, solo Qwen3-4B).
No lee ni importa código de análisis. Se niega a abrir la referencia si faltan salidas de probe.py.

  python comparar_nivel_c.py <carpeta> [<carpeta> ...]
"""
import json, sys, time
from pathlib import Path
import numpy as np
from scipy.stats import pearsonr, spearmanr

AQUI = Path(__file__).resolve().parent
R = AQUI.parent
TOL = 0.005
NECESARIOS = ("datos.json", "lectura_i.json", "barajadas.json", "puntajes_i.npz")
lado = lambda ic: "por encima" if ic[0] > 0 else ("por debajo" if ic[1] < 0 else "incluye 0")

for carpeta in sys.argv[1:]:
    S = AQUI / "salida" / "nivel_c" / carpeta
    faltan = [n for n in NECESARIOS if not (S / n).exists()]
    if faltan:
        raise SystemExit(f"{carpeta}: faltan salidas de probe.py ({faltan}); no se abre la referencia.")
    escrito = max((S / n).stat().st_mtime for n in NECESARIOS)
    modelo = carpeta.replace("_proofnetverif", "")
    ref = json.loads((R / "nivel_c" / "resultados" / f"resultados_c_{modelo}.json").read_text(encoding="utf-8"))
    mio = json.loads((S / "lectura_i.json").read_text(encoding="utf-8"))
    p = ref["C1"]["principal"]
    filas = {}
    for nombre, clave, valor, ic in (("AUROC(completo)", "completo", p["a"]["auroc"], p["a"]["ic"]),
                                     ("AUROC(solo_lean)", "solo_lean", p["b"]["auroc"], p["b"]["ic"]),
                                     ("Δ", "delta", p["diferencia"]["punto"], p["diferencia"]["ic"])):
        v = mio[clave]
        filas[nombre] = {"probe": list(v), "referencia": [valor, *ic], "diferencia": v[0] - valor, "dentro": abs(v[0] - valor) <= TOL}
    lados = {"probe": lado(mio["delta"][1:]), "referencia": lado(p["diferencia"]["ic"])}
    zp = np.load(S / "puntajes_i.npz"); zr = np.load(R / "nivel_c" / "resultados" / f"puntajes_c_{modelo}.npz")
    corr = {v: {"pearson": float(pearsonr(zp[v], zr["c1_" + v])[0]), "spearman": float(spearmanr(zp[v], zr["c1_" + v])[0]),
                "max_dif_abs": float(np.abs(zp[v] - zr["c1_" + v]).max())} for v in ("completo", "solo_lean")}
    capas = {}
    for v in ("completo", "solo_lean"):
        plano = [c for s in mio["capas_por_semilla_y_particion"][v] for c in s]
        cr = ref["C1"]["auroc_" + v]["capas_elegidas"]
        capas[v] = {"probe": mio["capas_por_semilla_y_particion"][v], "referencia": cr,
                    "iguales": sum(int(a == b) for a, b in zip(plano, cr)), "de": len(plano),
                    "distintas": [{"semilla": i // 5, "particion": i % 5, "probe": a, "referencia": b} for i, (a, b) in enumerate(zip(plano, cr)) if a != b]}
    res = {
        "carpeta": carpeta,
        "salidas_escritas": time.strftime("%Y-%m-%d %H:%M:%S %z", time.localtime(escrito)),
        "referencia_abierta": time.strftime("%Y-%m-%d %H:%M:%S %z"),
        "referencia": {k: ref.get(k) for k in ("modelo", "revision", "fecha", "n", "n_pos", "n_grupos", "grupos_por_tipo", "semillas", "n_boot")},
        "datos": json.loads((S / "datos.json").read_text(encoding="utf-8")),
        "barajadas": json.loads((S / "barajadas.json").read_text(encoding="utf-8")),
        "lecturas": {"i": {"cantidades": filas, "decision": lados, "misma_decision": lados["probe"] == lados["referencia"],
                           "y_identico": bool(np.array_equal(zp["y"], zr["y"])), "grupos_identicos": bool(np.array_equal(zp["grupos"], zr["g"])),
                           "correlacion_fila_a_fila": corr, "capas": capas, "segundos_probe": mio["segundos_cpu_de_las_diez_corridas"]}},
    }
    res["todo_dentro_de_tolerancia"] = all(f["dentro"] for f in filas.values())
    res["misma_decision_en_las_dos"] = lados["probe"] == lados["referencia"]
    seg = R / "nivel_c" / "segunda_implementacion" / "resultado_c1.json"
    if modelo == "qwen3_4b" and seg.exists():
        res["segunda_implementacion_json"] = json.loads(seg.read_text(encoding="utf-8"))
    (S / "comparacion.json").write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"\n== {carpeta}: dentro de {TOL}: {res['todo_dentro_de_tolerancia']}; misma decisión: {res['misma_decision_en_las_dos']}")
    for nombre, f in filas.items():
        a, b = f["probe"], f["referencia"]
        print(f"  {nombre:17s} {a[0]:.4f} [{a[1]:.4f}, {a[2]:.4f}]  ref {b[0]:.4f} [{b[1]:.4f}, {b[2]:.4f}]  dif {f['diferencia']:+.4f}  {'sí' if f['dentro'] else 'NO'}")
    print(f"  decisión: {lados}; y idéntico: {res['lecturas']['i']['y_identico']}; grupos idénticos: {res['lecturas']['i']['grupos_identicos']}; " +
          "; ".join(f"{v}: r={c['pearson']:.4f} rho={c['spearman']:.4f} max={c['max_dif_abs']:.3f}" for v, c in corr.items()))
    print("  capas iguales: " + "; ".join(f"{v} {c['iguales']}/{c['de']} {c['distintas']}" for v, c in capas.items()))
    b = res["barajadas"]
    print(f"  barajadas capas {b['capas']}: media {[round(x, 3) for x in b['auroc_media']]}, rango {np.min(b['todas']):.3f} a {np.max(b['todas']):.3f}")
    if "segunda_implementacion_json" in res:
        print("  segunda implementación:", json.dumps(res["segunda_implementacion_json"], ensure_ascii=False)[:900])
