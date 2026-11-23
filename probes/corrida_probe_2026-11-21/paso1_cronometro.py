import sys, time
from pathlib import Path
import numpy as np
R = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R))
import probe
from threadpoolctl import threadpool_info
print([(i["internal_api"], i["num_threads"]) for i in threadpool_info()])
for pos, capas in (("media_lean", (24,)), ("ultimo", (0, 12, 24, 36))):
    X, y, g, man = probe.cargar(probe.CARPETA, "completo", pos)
    f = probe.subconjunto(man, True); X, y, g = X[f], y[f], g[f]
    parts = probe.particiones_agrupadas(y, g, 5, 0)
    ent, pru = parts[0]
    for c in capas:
        t = time.perf_counter()
        p = probe._ajustar_y_puntuar(X[ent, c, :], y[ent], X[pru, c, :])
        dt = time.perf_counter() - t
        # ajuste interno (tamaño ~288) para la anidada
        internas = probe.particiones_agrupadas(y[ent], g[ent], 5, 0)
        e2, p2 = internas[0]
        t = time.perf_counter()
        probe._ajustar_y_puntuar(X[ent][e2, c, :], y[ent][e2], X[ent][p2, c, :])
        dt2 = time.perf_counter() - t
        print(f"{pos} capa {c:2d}: ajuste externo ({len(ent)} filas) {dt:.2f} s; interno ({len(e2)} filas) {dt2:.2f} s; AUROC fold {probe.auroc(y[pru], p):.3f}")
