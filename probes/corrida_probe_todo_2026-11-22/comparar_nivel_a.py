"""Compara las salidas de correr_nivel_a.py con los resultados de la referencia (Nivel A).

Solo lee resultados: referencia/v2_resultados_<modelo>.json y sus dos .npz. No lee ni
importa código de análisis de la referencia. Se niega a abrir la referencia de un modelo si
sus salidas de probe.py no están completas en disco.

  python comparar_nivel_a.py <modelo> [<modelo> ...]
"""
import json, sys, time
from pathlib import Path

import numpy as np
from scipy.stats import pearsonr, spearmanr

AQUI = Path(__file__).resolve().parent
R = AQUI.parent
REF = R / "referencia"
TOL = 0.005
LECTURAS = {"i": "i_ultimo_cv", "ii": "ii_media_lean_capa_fija"}
NECESARIOS = ("datos.json", "lectura_i.json", "lectura_ii.json", "barajadas.json", "puntajes_i.npz", "puntajes_ii.npz")


def lado(ic):
    return "por encima" if ic[0] > 0 else ("por debajo" if ic[1] < 0 else "incluye 0")


def comparar(modelo):
    S = AQUI / "salida" / "nivel_a" / modelo
    faltan = [n for n in NECESARIOS if not (S / n).exists()]
    if faltan:
        raise SystemExit(f"{modelo}: faltan salidas de probe.py ({faltan}); no se abre la referencia.")
    escrito = max((S / n).stat().st_mtime for n in NECESARIOS)
    abierto = time.time()
    ref = json.loads((REF / f"v2_resultados_{modelo}.json").read_text(encoding="utf-8"))
    res = {
        "modelo": modelo,
        "salidas_escritas": time.strftime("%Y-%m-%d %H:%M:%S %z", time.localtime(escrito)),
        "referencia_abierta": time.strftime("%Y-%m-%d %H:%M:%S %z", time.localtime(abierto)),
        "referencia": {k: ref.get(k) for k in ("modelo", "revision", "fecha", "n", "n_pos", "n_capas_mas_embeddings", "capa_fija_lectura_ii", "semillas", "n_boot")},
        "datos": json.loads((S / "datos.json").read_text(encoding="utf-8")),
        "barajadas": json.loads((S / "barajadas.json").read_text(encoding="utf-8")),
        "lecturas": {},
    }
    todo_dentro, misma = True, True
    for corta, larga in LECTURAS.items():
        mio = json.loads((S / f"lectura_{corta}.json").read_text(encoding="utf-8"))
        r = ref["lecturas"][larga]
        filas = {}
        for nombre, clave_p, clave_r, clave_ic in (
            ("AUROC(completo)", "completo", "auroc_completo", "ic_completo"),
            ("AUROC(solo_lean)", "solo_lean", "auroc_solo_lean", "ic_solo_lean"),
            ("Δ", "delta", "delta", "ic_delta"),
        ):
            p, lo, hi = mio[clave_p]
            dif = p - r[clave_r]
            filas[nombre] = {"probe": [p, lo, hi], "referencia": [r[clave_r], *r[clave_ic]], "diferencia": dif, "dentro": abs(dif) <= TOL}
            todo_dentro &= abs(dif) <= TOL
        lados = {"probe": lado(mio["delta"][1:]), "referencia": lado(r["ic_delta"])}
        misma &= lados["probe"] == lados["referencia"]

        zp = np.load(S / f"puntajes_{corta}.npz")
        zr = np.load(REF / f"v2_puntajes_{modelo}_{larga}.npz")
        y_igual = bool(np.array_equal(zp["y"], zr["y"]))
        corr = {}
        for v in ("completo", "solo_lean"):
            a, b = zp[v], zr[v]
            corr[v] = {"pearson": float(pearsonr(a, b)[0]), "spearman": float(spearmanr(a, b)[0]),
                       "max_dif_abs": float(np.abs(a - b).max())}
        entrada = {"cantidades": filas, "decision": lados, "misma_decision": lados["probe"] == lados["referencia"],
                   "y_identico": y_igual, "correlacion_fila_a_fila": corr}
        if corta == "i":
            capas_p = mio["capas_por_semilla_y_particion"]
            capas_r = r["capas_elegidas"]
            entrada["capas"] = {}
            for v in ("completo", "solo_lean"):
                plano = [c for s in capas_p[v] for c in s]
                iguales = sum(int(a == b) for a, b in zip(plano, capas_r[v]))
                distintas = [{"semilla": i // 5, "particion": i % 5, "probe": a, "referencia": b}
                             for i, (a, b) in enumerate(zip(plano, capas_r[v])) if a != b]
                entrada["capas"][v] = {"probe": capas_p[v], "referencia": capas_r[v], "iguales": iguales,
                                       "de": len(plano), "distintas": distintas}
        else:
            entrada["capa"] = {"probe": mio["capa"], "referencia": ref.get("capa_fija_lectura_ii")}
        entrada["segundos_probe"] = mio["segundos"]
        res["lecturas"][corta] = entrada
    res["todo_dentro_de_tolerancia"] = bool(todo_dentro)
    res["misma_decision_en_las_dos"] = bool(misma)

    if modelo == "qwen3_4b":  # corrida del 21 nov (máquina Linux)
        V = R / "corrida_probe_2026-11-21" / "salida"
        linux = {}
        for corta in LECTURAS:
            a, b = np.load(S / f"puntajes_{corta}.npz"), np.load(V / f"puntajes_{corta}.npz")
            linux[corta] = {v: {"max_dif_abs": float(np.abs(a[v] - b[v]).max()), "identico": bool(np.array_equal(a[v], b[v]))}
                            for v in ("completo", "solo_lean")}
            ja = json.loads((S / f"lectura_{corta}.json").read_text(encoding="utf-8"))
            jb = json.loads((V / f"lectura_{corta}.json").read_text(encoding="utf-8"))
            linux[corta]["max_dif_resumen"] = max(abs(x - y) for k in ("completo", "solo_lean", "delta") for x, y in zip(ja[k], jb[k]))
            if corta == "i":
                linux[corta]["capas_iguales"] = ja["capas_por_semilla_y_particion"] == jb["capas_por_semilla_y_particion"]
        ba = json.loads((S / "barajadas.json").read_text(encoding="utf-8"))
        bb = json.loads((V / "barajadas.json").read_text(encoding="utf-8"))
        linux["barajadas_max_dif"] = float(np.abs(np.array(ba["todas"]) - np.array(bb["todas"])).max())
        res["frente_a_corrida_linux_2026-11-21"] = linux
    return res


if __name__ == "__main__":
    for modelo in sys.argv[1:]:
        res = comparar(modelo)
        destino = AQUI / "salida" / "nivel_a" / modelo / "comparacion.json"
        destino.write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\n== {modelo}: dentro de {TOL}: {res['todo_dentro_de_tolerancia']}; misma decisión: {res['misma_decision_en_las_dos']}")
        for corta, e in res["lecturas"].items():
            for nombre, f in e["cantidades"].items():
                p, r = f["probe"], f["referencia"]
                print(f"  ({corta}) {nombre:17s} {p[0]:.4f} [{p[1]:.4f}, {p[2]:.4f}]  ref {r[0]:.4f} [{r[1]:.4f}, {r[2]:.4f}]  dif {f['diferencia']:+.4f}  {'sí' if f['dentro'] else 'NO'}")
            print(f"  ({corta}) decisión: {e['decision']}; y idéntico: {e['y_identico']}; " +
                  "; ".join(f"{v}: r={c['pearson']:.4f} rho={c['spearman']:.4f} max={c['max_dif_abs']:.3f}" for v, c in e["correlacion_fila_a_fila"].items()))
            if "capas" in e:
                print("  (i) capas iguales: " + "; ".join(f"{v} {c['iguales']}/{c['de']} {c['distintas']}" for v, c in e["capas"].items()))
        b = res["barajadas"]
        print(f"  barajadas capas {b['capas']}: media {[round(x, 3) for x in b['auroc_media']]}, rango {np.min(b['todas']):.3f} a {np.max(b['todas']):.3f}")
        if "frente_a_corrida_linux_2026-11-21" in res:
            print("  frente a Linux 21 nov:", json.dumps(res["frente_a_corrida_linux_2026-11-21"]))
