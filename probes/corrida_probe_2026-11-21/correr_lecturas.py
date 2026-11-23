"""Corre las dos lecturas del Nivel A con las funciones de probe.py, sin modificarlo.

Por qué existe: la terminal de esta sesión corta cada orden a los 180 s y no deja procesos
en segundo plano, y main() entero tarda más que eso. Este archivo llama a las mismas
funciones, con los mismos argumentos que main(), una pieza por orden, y guarda cada pieza.
No ajusta ningún modelo por su cuenta ni cambia ningún parámetro.

  python correr_lecturas.py ii                      lectura (ii): media_lean, capa fija
  python correr_lecturas.py i <variante> <semilla>  una corrida de elegir_capa_anidada
  python correr_lecturas.py i_cierre                promedia semillas; IC y diferencia
  python correr_lecturas.py barajadas               control_barajadas en las capas 12, 24, 36
"""
import hashlib, json, sys, time
from pathlib import Path
import numpy as np
R = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R))
import probe

SALIDA = Path(__file__).resolve().parent / "salida"
SALIDA.mkdir(exist_ok=True)
SHA = hashlib.sha256((R / "probe.py").read_bytes()).hexdigest()
etapa = sys.argv[1]
t0 = time.perf_counter()


def datos(variante, posicion):
    X, y, grupos, manifiesto = probe.cargar(probe.CARPETA, variante, posicion)
    filas = probe.subconjunto(manifiesto, True)
    X, y, grupos = X[filas], y[filas], grupos[filas]
    probe._verificar_conteos(y, True)
    return X, y, grupos, filas


def resumen(y, grupos, p_comp, p_lean):
    # Las mismas tres llamadas que hace main().
    return {
        "completo": probe.ic_bootstrap(y, p_comp, grupos, semilla=probe.SEMILLA),
        "solo_lean": probe.ic_bootstrap(y, p_lean, grupos, semilla=probe.SEMILLA),
        "delta": probe.diferencia_pareada(y, p_comp, p_lean, grupos, semilla=probe.SEMILLA),
    }


def escribir(nombre, res, extra):
    res = {"sha256_probe_py": SHA, **res, **extra, "segundos": round(time.perf_counter() - t0, 1)}
    (SALIDA / f"{nombre}.json").write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(res, ensure_ascii=False, indent=2))


if etapa == "ii":
    X_comp, y, grupos, filas = datos("completo", "media_lean")
    X_lean = datos("solo_lean", "media_lean")[0]
    capa = (2 * (X_comp.shape[1] - 1)) // 3
    # curva_por_capa sobre esa sola capa: el puntaje de una capa no depende de las otras.
    p_comp = probe.curva_por_capa(X_comp[:, capa:capa + 1, :], y, grupos, semillas=probe.SEMILLAS, n_boot=0, verboso=False)["puntajes"][0]
    p_lean = probe.curva_por_capa(X_lean[:, capa:capa + 1, :], y, grupos, semillas=probe.SEMILLAS, n_boot=0, verboso=False)["puntajes"][0]
    np.savez(SALIDA / "puntajes_ii.npz", filas=filas, y=y, grupos=grupos, completo=p_comp, solo_lean=p_lean)
    escribir("lectura_ii", resumen(y, grupos, p_comp, p_lean), {"capa": capa, "semillas": list(probe.SEMILLAS)})
elif etapa == "i":
    variante, semilla = sys.argv[2], int(sys.argv[3])
    X, y, grupos, filas = datos(variante, "ultimo")
    puntajes, capas = probe.elegir_capa_anidada(X, y, grupos, semilla=semilla)
    np.savez(SALIDA / f"puntajes_i_{variante}_s{semilla}.npz", filas=filas, y=y, grupos=grupos, puntajes=puntajes, capas=np.array(capas))
    print(variante, "semilla", semilla, "capas", capas, f"{time.perf_counter() - t0:.0f} s")
elif etapa == "i_cierre":
    _, y, grupos, filas = datos("completo", "ultimo")
    p, capas = {}, {}
    for variante in ("completo", "solo_lean"):
        corridas = [np.load(SALIDA / f"puntajes_i_{variante}_s{s}.npz") for s in probe.SEMILLAS]
        assert all(np.array_equal(c["filas"], filas) for c in corridas)
        p[variante] = np.mean([c["puntajes"] for c in corridas], axis=0)  # como _anidada_promediada
        capas[variante] = [c["capas"].tolist() for c in corridas]
    np.savez(SALIDA / "puntajes_i.npz", filas=filas, y=y, grupos=grupos, completo=p["completo"], solo_lean=p["solo_lean"])
    escribir("lectura_i", resumen(y, grupos, p["completo"], p["solo_lean"]), {"capas_por_semilla_y_particion": capas, "semillas": list(probe.SEMILLAS)})
elif etapa == "barajadas":
    X_comp, y, grupos, filas = datos("completo", "ultimo")
    capas = [12, 24, 36]
    b = probe.control_barajadas(X_comp[:, capas, :], y, grupos, semilla=probe.SEMILLA)
    escribir("barajadas", {"capas": capas, "auroc_media": b["auroc"].tolist(), "std": b["std"].tolist(), "todas": b["todas"].tolist()}, {})
else:
    raise SystemExit(__doc__)
