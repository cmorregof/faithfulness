"""Cronometra _ajustar_y_puntuar de probe.py con el tamaño del Nivel C. No calcula ninguna métrica con etiquetas reales sobre puntajes: solo tiempos."""
import sys, time
from pathlib import Path
import numpy as np
R = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R))
import probe
C = R / "nivel_c" / "activaciones" / sys.argv[1]
X, y, g, man = probe.cargar(C, "completo", "ultimo")
ent, pru = probe.particiones_agrupadas(y, g, 5, 0)[0]
e2, p2 = probe.particiones_agrupadas(y[ent], g[ent], 5, 0)[0]
for c in (1, X.shape[1] // 2, X.shape[1] - 1):
    t = time.perf_counter(); probe._ajustar_y_puntuar(X[ent, c, :], y[ent], X[pru, c, :]); dt = time.perf_counter() - t
    t = time.perf_counter(); probe._ajustar_y_puntuar(X[ent][e2, c, :], y[ent][e2], X[ent][p2, c, :]); dt2 = time.perf_counter() - t
    print(f"{sys.argv[1]} capa {c}: externo ({len(ent)} filas) {dt:.2f} s; interno ({len(e2)} filas) {dt2:.2f} s", flush=True)
