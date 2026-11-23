"""Cronometra _ajustar_y_puntuar de probe.py (sin modificarlo) en qwen3_4b, 450 filas."""
import os, sys, time
from pathlib import Path
import numpy as np
R = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R))
import probe
from threadpoolctl import threadpool_info
print({k: os.environ.get(k) for k in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "VECLIB_MAXIMUM_THREADS")})
print([(i["internal_api"], i["num_threads"]) for i in threadpool_info()])
for pos, capas in (("media_lean", (24,)), ("ultimo", (0, 12, 24, 36))):
    X, y, g, man = probe.cargar(probe.CARPETA, "completo", pos)
    f = probe.subconjunto(man, True); X, y, g = X[f], y[f], g[f]
    ent, pru = probe.particiones_agrupadas(y, g, 5, 0)[0]
    e2, p2 = probe.particiones_agrupadas(y[ent], g[ent], 5, 0)[0]
    for c in capas:
        ts = []
        for _ in range(3):
            t = time.perf_counter()
            p = probe._ajustar_y_puntuar(X[ent, c, :], y[ent], X[pru, c, :])
            ts.append(time.perf_counter() - t)
        t = time.perf_counter()
        probe._ajustar_y_puntuar(X[ent][e2, c, :], y[ent][e2], X[ent][p2, c, :])
        dt2 = time.perf_counter() - t
        print(f"{pos} capa {c:2d}: externo ({len(ent)} filas) {min(ts):.3f} s (3 rep: {' '.join(f'{x:.3f}' for x in ts)}); interno ({len(e2)} filas) {dt2:.3f} s; AUROC fold {probe.auroc(y[pru], p):.4f}; suma puntajes {p.sum()!r}")
