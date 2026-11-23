"""Corre las dos lecturas del Nivel A con las funciones de probe.py, sin modificarlo.

Adaptado de corrida_probe_2026-11-21/correr_lecturas.py. Solo cambia que la carpeta de
activaciones es un argumento, que las capas de las barajadas se calculan a partir del número
de bloques L del modelo, y que las piezas ya escritas no se repiten. Llama a las mismas
funciones de probe.py, con los mismos argumentos que main(). No ajusta ningún modelo por su
cuenta, no cambia ningún parámetro y no abre nada de referencia/.

  python correr_nivel_a.py <modelo>                 todo: datos, ii, i, barajadas
  python correr_nivel_a.py <modelo> datos           forma, dtype y conteos del manifiesto
  python correr_nivel_a.py <modelo> ii              lectura (ii): media_lean, capa fija ⌊2L/3⌋
  python correr_nivel_a.py <modelo> i               lectura (i): ultimo, capa anidada, semillas 0 a 4
  python correr_nivel_a.py <modelo> barajadas       control_barajadas en ⌊L/3⌋, ⌊2L/3⌋ y L de ultimo

<modelo> es el nombre de una carpeta de probes/activaciones/ (p. ej. olmo2_7b).
"""
import hashlib, json, os, platform, sys, time
from pathlib import Path

import numpy as np

AQUI = Path(__file__).resolve().parent
R = AQUI.parent
sys.path.insert(0, str(R))
import probe  # noqa: E402

SHA_ESPERADO = "bbdb16350b88494e7c1c6a0d5c51b3003ea41d690327378fb58f06dc697dc30f"
SHA = hashlib.sha256((R / "probe.py").read_bytes()).hexdigest()
if SHA != SHA_ESPERADO:
    raise SystemExit(f"probe.py no tiene el SHA esperado: {SHA}")
SHA_ORQ = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

if len(sys.argv) < 2:
    raise SystemExit(__doc__)
MODELO = sys.argv[1]
ETAPAS = sys.argv[2:] or ["datos", "ii", "i", "barajadas"]
CARPETA = R / "activaciones" / MODELO
SALIDA = AQUI / "salida" / "nivel_a" / MODELO
SALIDA.mkdir(parents=True, exist_ok=True)


def entorno():
    import scipy, sklearn
    return {
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scikit-learn": sklearn.__version__,
        "scipy": scipy.__version__,
        "plataforma": platform.platform(),
        "hilos": {k: os.environ.get(k) for k in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "VECLIB_MAXIMUM_THREADS")},
    }


def datos(variante, posicion):
    X, y, grupos, manifiesto = probe.cargar(CARPETA, variante, posicion)
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


def escribir(nombre, res, extra, t0):
    res = {
        "modelo": MODELO, "sha256_probe_py": SHA, "sha256_correr_nivel_a_py": SHA_ORQ,
        **res, **extra, "entorno": entorno(), "segundos": round(time.perf_counter() - t0, 1),
    }
    (SALIDA / f"{nombre}.json").write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(res, ensure_ascii=False, indent=2), flush=True)


def etapa_datos():
    t0 = time.perf_counter()
    formas = {}
    for variante in ("completo", "solo_lean"):
        for posicion in ("ultimo", "media_lean"):
            a = np.load(CARPETA / f"acts_{variante}_{posicion}.npy", mmap_mode="r")
            formas[f"{variante}_{posicion}"] = {"forma": list(a.shape), "dtype": str(a.dtype)}
    if len({json.dumps(f) for f in formas.values()}) != 1:
        raise SystemExit(f"{MODELO}: las cuatro matrices no tienen la misma forma y dtype: {formas}")
    _, y, grupos, filas = datos("completo", "ultimo")
    n_capas = formas["completo_ultimo"]["forma"][1]
    escribir("datos", {
        "formas": formas, "bloques_L": n_capas - 1,
        "filas": len(filas), "positivas": int((y == 1).sum()), "negativas": int((y == 0).sum()),
        "grupos": len(set(grupos.tolist())),
        "sha256_manifiesto": hashlib.sha256((CARPETA / "manifiesto.jsonl").read_bytes()).hexdigest(),
    }, {}, t0)


def etapa_ii():
    t0 = time.perf_counter()
    X_comp, y, grupos, filas = datos("completo", "media_lean")
    X_lean = datos("solo_lean", "media_lean")[0]
    capa = (2 * (X_comp.shape[1] - 1)) // 3
    # curva_por_capa sobre esa sola capa: el puntaje de una capa no depende de las otras.
    p_comp = probe.curva_por_capa(X_comp[:, capa:capa + 1, :], y, grupos, semillas=probe.SEMILLAS, n_boot=0, verboso=False)["puntajes"][0]
    p_lean = probe.curva_por_capa(X_lean[:, capa:capa + 1, :], y, grupos, semillas=probe.SEMILLAS, n_boot=0, verboso=False)["puntajes"][0]
    np.savez(SALIDA / "puntajes_ii.npz", filas=filas, y=y, grupos=grupos, completo=p_comp, solo_lean=p_lean)
    escribir("lectura_ii", resumen(y, grupos, p_comp, p_lean), {"capa": capa, "semillas": list(probe.SEMILLAS)}, t0)


def etapa_i():
    t0 = time.perf_counter()
    p, capas, filas, y, grupos = {}, {}, None, None, None
    for variante in ("completo", "solo_lean"):
        X, y, grupos, filas = datos(variante, "ultimo")
        corridas = []
        for semilla in probe.SEMILLAS:
            ruta = SALIDA / f"puntajes_i_{variante}_s{semilla}.npz"
            if not ruta.exists():
                t1 = time.perf_counter()
                puntajes, capas_s = probe.elegir_capa_anidada(X, y, grupos, semilla=semilla)
                np.savez(ruta, filas=filas, y=y, grupos=grupos, puntajes=puntajes, capas=np.array(capas_s))
                print(variante, "semilla", semilla, "capas", capas_s, f"{time.perf_counter() - t1:.0f} s", flush=True)
            c = np.load(ruta)
            assert np.array_equal(c["filas"], filas)
            corridas.append(c)
        p[variante] = np.mean([c["puntajes"] for c in corridas], axis=0)  # como _anidada_promediada
        capas[variante] = [c["capas"].tolist() for c in corridas]
    np.savez(SALIDA / "puntajes_i.npz", filas=filas, y=y, grupos=grupos, completo=p["completo"], solo_lean=p["solo_lean"])
    escribir("lectura_i", resumen(y, grupos, p["completo"], p["solo_lean"]),
             {"capas_por_semilla_y_particion": capas, "semillas": list(probe.SEMILLAS)}, t0)


def etapa_barajadas():
    t0 = time.perf_counter()
    X_comp, y, grupos, _ = datos("completo", "ultimo")
    L = X_comp.shape[1] - 1
    capas = [L // 3, (2 * L) // 3, L]
    b = probe.control_barajadas(X_comp[:, capas, :], y, grupos, semilla=probe.SEMILLA)
    escribir("barajadas", {"posicion": "ultimo", "capas": capas, "auroc_media": b["auroc"].tolist(),
                           "std": b["std"].tolist(), "todas": b["todas"].tolist()}, {}, t0)


for etapa in ETAPAS:
    print(f"== {MODELO}: {etapa} ==", flush=True)
    {"datos": etapa_datos, "ii": etapa_ii, "i": etapa_i, "barajadas": etapa_barajadas}[etapa]()
