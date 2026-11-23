"""Corre la prueba central del Nivel C (C1) con las funciones de probe.py, sin modificarlo.

C1, según nivel_c/regla_borrador.md §4: todas las filas de ProofNetVerif, posición «ultimo»,
capa por validación anidada independiente en cada condición, particiones agrupadas por
enunciado, semillas 0 a 4, Δ = AUROC(completo) − AUROC(solo_lean) sobre los puntajes fuera de
partición promediados entre semillas, e IC por bootstrap de grupos estratificado por tipo de
grupo (2000 remuestreos, semilla 0).

Este archivo solo carga los datos con probe.cargar (que arma y y grupos a partir del
manifiesto) y llama a elegir_capa_anidada, ic_bootstrap, diferencia_pareada y
control_barajadas con los mismos argumentos que main(). No llama a subconjunto ni a
_verificar_conteos, porque en el Nivel C no hay filtro de compilación. No escribe ninguna
lógica de análisis y no abre nivel_c/resultados/ ni nivel_c/segunda_implementacion/.

  python correr_nivel_c.py <carpeta> datos
  python correr_nivel_c.py <carpeta> i <variante> <semilla>   una corrida de elegir_capa_anidada
  python correr_nivel_c.py <carpeta> i_cierre                 promedia semillas; IC y diferencia
  python correr_nivel_c.py <carpeta> barajadas                control_barajadas en ⌊L/3⌋, ⌊2L/3⌋ y L

<carpeta> es el nombre de una carpeta de probes/nivel_c/activaciones/.
"""
import hashlib, json, os, platform, sys, time
from pathlib import Path

import numpy as np

AQUI = Path(__file__).resolve().parent
R = AQUI.parent
sys.path.insert(0, str(R))
import probe  # noqa: E402

SHA = hashlib.sha256((R / "probe.py").read_bytes()).hexdigest()
if SHA != "bbdb16350b88494e7c1c6a0d5c51b3003ea41d690327378fb58f06dc697dc30f":
    raise SystemExit(f"probe.py no tiene el SHA esperado: {SHA}")
SHA_ORQ = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

if len(sys.argv) < 3:
    raise SystemExit(__doc__)
NOMBRE, ETAPA = sys.argv[1], sys.argv[2]
CARPETA = R / "nivel_c" / "activaciones" / NOMBRE
SALIDA = AQUI / "salida" / "nivel_c" / NOMBRE
SALIDA.mkdir(parents=True, exist_ok=True)
POSICION = "ultimo"
t0 = time.perf_counter()


def entorno():
    import scipy, sklearn
    return {
        "python": platform.python_version(), "numpy": np.__version__, "scikit-learn": sklearn.__version__,
        "scipy": scipy.__version__, "plataforma": platform.platform(),
        "hilos": {k: os.environ.get(k) for k in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "VECLIB_MAXIMUM_THREADS")},
    }


def datos(variante):
    X, y, grupos, _ = probe.cargar(CARPETA, variante, POSICION)
    return X, y, grupos


def escribir(nombre, res):
    res = {"carpeta": NOMBRE, "sha256_probe_py": SHA, "sha256_correr_nivel_c_py": SHA_ORQ, **res,
           "entorno": entorno(), "segundos": round(time.perf_counter() - t0, 1)}
    (SALIDA / f"{nombre}.json").write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(res, ensure_ascii=False, indent=2), flush=True)


if ETAPA == "datos":
    formas = {}
    for variante in ("completo", "solo_lean"):
        a = np.load(CARPETA / f"acts_{variante}_{POSICION}.npy", mmap_mode="r")
        formas[variante] = {"forma": list(a.shape), "dtype": str(a.dtype)}
    manifiesto = [json.loads(l) for l in open(CARPETA / "manifiesto.jsonl", encoding="utf-8") if l.strip()]
    y = np.array([f["etiqueta"] for f in manifiesto])
    clases = {}
    for f in manifiesto:
        clases.setdefault(f["grupo"], set()).add(f["etiqueta"])
    tipos = {"mixto": 0, "solo_positivas": 0, "solo_negativas": 0}
    for s in clases.values():
        tipos["mixto" if len(s) == 2 else ("solo_positivas" if s == {1} else "solo_negativas")] += 1
    meta = json.loads((CARPETA / "meta.json").read_text(encoding="utf-8"))
    escribir("datos", {
        "formas": formas, "bloques_L": formas["completo"]["forma"][1] - 1,
        "idx_en_orden": [f["idx"] for f in manifiesto] == list(range(len(manifiesto))),
        "filas": len(y), "positivas": int((y == 1).sum()), "negativas": int((y == 0).sum()),
        "grupos": len(clases), "tipos_de_grupo": tipos,
        "modelo": meta.get("modelo"), "revision": meta.get("revision"),
        "sha256_manifiesto": hashlib.sha256((CARPETA / "manifiesto.jsonl").read_bytes()).hexdigest(),
    })
elif ETAPA == "i":
    variante, semilla = sys.argv[3], int(sys.argv[4])
    ruta = SALIDA / f"puntajes_i_{variante}_s{semilla}.npz"
    if ruta.exists():
        raise SystemExit(f"ya existe {ruta.name}")
    X, y, grupos = datos(variante)
    puntajes, capas = probe.elegir_capa_anidada(X, y, grupos, semilla=semilla)
    np.savez(ruta, y=y, grupos=grupos, puntajes=puntajes, capas=np.array(capas), segundos=time.perf_counter() - t0)
    print(NOMBRE, variante, "semilla", semilla, "capas", capas, f"{time.perf_counter() - t0:.0f} s", flush=True)
elif ETAPA == "i_cierre":
    p, capas, segundos, y, grupos = {}, {}, 0.0, None, None
    for variante in ("completo", "solo_lean"):
        corridas = [np.load(SALIDA / f"puntajes_i_{variante}_s{s}.npz") for s in probe.SEMILLAS]
        y, grupos = corridas[0]["y"], corridas[0]["grupos"]
        assert all(np.array_equal(c["y"], y) and np.array_equal(c["grupos"], grupos) for c in corridas)
        p[variante] = np.mean([c["puntajes"] for c in corridas], axis=0)  # como _anidada_promediada
        capas[variante] = [c["capas"].tolist() for c in corridas]
        segundos += sum(float(c["segundos"]) for c in corridas)
    np.savez(SALIDA / "puntajes_i.npz", y=y, grupos=grupos, completo=p["completo"], solo_lean=p["solo_lean"])
    # Las mismas tres llamadas que hace main().
    escribir("lectura_i", {
        "completo": probe.ic_bootstrap(y, p["completo"], grupos, semilla=probe.SEMILLA),
        "solo_lean": probe.ic_bootstrap(y, p["solo_lean"], grupos, semilla=probe.SEMILLA),
        "delta": probe.diferencia_pareada(y, p["completo"], p["solo_lean"], grupos, semilla=probe.SEMILLA),
        "posicion": POSICION, "capas_por_semilla_y_particion": capas, "semillas": list(probe.SEMILLAS),
        "segundos_cpu_de_las_diez_corridas": round(segundos, 1),
    })
elif ETAPA == "barajadas":
    X, y, grupos = datos("completo")
    L = X.shape[1] - 1
    capas = [L // 3, (2 * L) // 3, L]
    b = probe.control_barajadas(X[:, capas, :], y, grupos, semilla=probe.SEMILLA)
    escribir("barajadas", {"posicion": POSICION, "capas": capas, "auroc_media": b["auroc"].tolist(),
                           "std": b["std"].tolist(), "todas": b["todas"].tolist()})
else:
    raise SystemExit(__doc__)
