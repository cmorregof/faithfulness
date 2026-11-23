#!/usr/bin/env python3
"""mapas_desde_escaner.py — rehace escaner_out/mapa_<modelo>.npz, la entrada de escaner_v3.py (13 nov 2026).

Los mapa_*.npz originales se hicieron en otra sesión y no están en el Mac. Aquí se reconstruyen desde las salidas
crudas de paper_adecuacion/escaner.py, que sí están: escaner/<modelo>/escaner_<variante>.npy, de forma
(450, capas+1, 92), con el puntaje fuera de partición de cada fila en cada capa y columna, y direcciones.npz, que
guarda las etiquetas («y»). Cada celda del mapa es la AUROC de esos puntajes frente a la etiqueta, sobre las 450
filas juntas. Fila 0 = embeddings. Una columna sin tokens en alguna fila queda en NaN.

No corre ningún modelo; es aritmética sobre archivos guardados. Aprobado por Carlos el 13 de noviembre.
Uso:  <python con numpy> mapas_desde_escaner.py      (escribe figuras_v5/escaner_out/)
Al final imprime la comprobación contra las cifras del artículo («Where the separation is readable»).
"""
import os
import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
ESCANER = os.path.join(AQUI, "..", "..", "escaner")
SALIDA = os.path.join(AQUI, "escaner_out")
MODELOS = ("olmo2_7b", "gemma3_4b", "llama31_8b", "qwen3_4b", "qwen3_8b")
# diferencia media sobre los tokens de Lean en el 60 % superior de las capas, como la imprime el artículo
ARTICULO = {"qwen3_8b": 0.043, "qwen3_4b": 0.039, "llama31_8b": 0.031, "gemma3_4b": 0.024, "olmo2_7b": 0.012}


def rangos(x):
    """Rangos medios (empates promediados) a lo largo del eje 0."""
    orden = np.argsort(x, axis=0, kind="stable")
    r = np.empty_like(orden, dtype=np.float64)
    n = x.shape[0]
    np.put_along_axis(r, orden, np.arange(1, n + 1, dtype=np.float64)[:, None], axis=0)
    xs = np.take_along_axis(x, orden, axis=0)
    for j in range(x.shape[1]):                      # promedia rangos en los empates, columna por columna
        v = xs[:, j]
        if np.any(v[1:] == v[:-1]):
            _, inv, cnt = np.unique(v, return_inverse=True, return_counts=True)
            ini = np.cumsum(cnt) - cnt
            r[orden[:, j], j] = (ini + (cnt + 1) / 2.0)[inv]
    return r


def auroc_por_celda(P, y):
    """P: (N, capas+1, columnas); y: (N,) con 1 = fiel. Devuelve (capas+1, columnas)."""
    N, R, B = P.shape
    X = np.asarray(P, dtype=np.float64).reshape(N, R * B)
    malo = np.isnan(X).any(0)
    X = np.where(np.isnan(X), 0.0, X)
    n1 = int(y.sum()); n0 = N - n1
    a = (rangos(X)[y == 1].sum(0) - n1 * (n1 + 1) / 2.0) / (n1 * n0)
    a[malo] = np.nan
    return a.reshape(R, B).astype(np.float32)


def main():
    os.makedirs(SALIDA, exist_ok=True)
    for m in MODELOS:
        d = os.path.join(ESCANER, m)
        y = np.load(os.path.join(d, "direcciones.npz"))["y"].astype(int)
        mapas = {}
        for v in ("completo", "solo_lean"):
            P = np.load(os.path.join(d, f"escaner_{v}.npy"), mmap_mode="r")
            assert P.shape[0] == len(y) and np.load(os.path.join(d, f"hecho_{v}.npy")).all(), (m, v)
            mapas[v] = auroc_por_celda(P, y)
        np.savez(os.path.join(SALIDA, f"mapa_{m}.npz"), **mapas)
        c, s = mapas["completo"], mapas["solo_lean"]
        R = c.shape[0]
        arriba = round(0.4 * (R - 1))                    # 60 % superior de las capas; con esta fila inicial
        dif = float(np.nanmean(c[arriba:, 44:84] - s[arriba:, 44:84]))   # los cinco modelos dan la cifra impresa
        assert f"{dif:+.3f}" == f"{ARTICULO[m]:+.3f}", (m, dif)
        nl = float(np.nanmean(c[:, 2:42]))
        print(f"{m:11s} filas {len(y)} (fieles {int(y.sum())})  capas+1 {R}  Lean, 60% superior: {dif:+.3f} "
              f"(artículo {ARTICULO[m]:+.3f})  enunciado, media: {nl:.3f}  NaN completo {int(np.isnan(c).sum())}, solo_lean {int(np.isnan(s).sum())}")


if __name__ == "__main__":
    main()
