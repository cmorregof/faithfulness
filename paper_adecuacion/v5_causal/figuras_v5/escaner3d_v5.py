#!/usr/bin/env python3
"""escaner3d_v5.py — relieve 3D de los mapas para el README del repositorio (13 nov 2026). No va en el artículo.

Usa el relieve de escaner_v3.py (una rebanada por capa, la primera delante; alto y color = AUROC de la sonda que lee
enunciado y Lean; línea oscura = el Lean solo) con los mismos mapas de la figura del artículo
(figuras_v5/escaner_out/, ver mapas_desde_escaner.py). Cambia el tamaño y el texto, pensados para verse a unos
830 px de ancho en GitHub, con fondo blanco opaco para que también se lea en modo oscuro.

A diferencia de la figura 2D, el relieve suaviza un poco a lo largo de la posición (gaussiana, sigma = 1 columna)
y deja en la línea de base las celdas por debajo del azar. La imagen lo dice.

Escribe en figuras_v5/readme/:  relieve_cinco_modelos.png  y  relieve_<modelo>.png
Necesita numpy, matplotlib, colorspacious y tueplots. No usa LaTeX ni scipy.
Uso:  <python> escaner3d_v5.py [modelo de la imagen individual, por defecto qwen3_4b]
"""
import glob
import os
import sys

AQUI = os.path.dirname(os.path.abspath(__file__))
os.environ.setdefault("ESCANER_DATOS", os.path.join(AQUI, "escaner_out"))

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager as fm

import escaner_v3 as E

for f in glob.glob("/usr/local/texlive/*/texmf-dist/fonts/opentype/public/lm/lmroman10-*.otf"):
    fm.fontManager.addfont(f)
plt.rcParams.update({"text.usetex": False, "font.family": "serif", "font.serif": ["Latin Modern Roman", "DejaVu Serif"],
                     "mathtext.fontset": "cm", "savefig.dpi": 200, "figure.facecolor": "white", "savefig.facecolor": "white"})
TEXTO, CENIZA = E.TEXTO, E.CENIZA
SALIDA = os.path.join(AQUI, "readme")
SIGMA = 1.0


def suavizar(z):
    """Gaussiana a lo largo de la posición, sigma = 1 columna, bordes repetidos (igual que gaussian_filter1d de scipy
    con truncate = 4 y mode = 'nearest'), escrita con numpy para no depender de scipy."""
    r = int(4 * SIGMA + 0.5)
    k = np.exp(-0.5 * (np.arange(-r, r + 1) / SIGMA) ** 2)
    k /= k.sum()
    return np.convolve(np.pad(np.asarray(z, float), r, mode="edge"), k, mode="valid")


E.suavizar = suavizar


def clave(fig, rect, modelos, fs):
    ax = fig.add_axes(rect)
    n = len(modelos)
    for j, m in enumerate(modelos):
        ax.imshow(np.linspace(0, 1, 256)[None], aspect="auto", cmap=E.rampa(m), extent=(E.VMIN, E.VMAX, n - j - 1, n - j - 0.16))
    ax.set_ylim(0, n); ax.set_xlim(E.VMIN, E.VMAX); ax.set_yticks([])
    ax.set_xticks([0.5, 0.55, 0.6, 0.65, 0.7]); ax.set_xticklabels(["0.50", "0.55", "0.60", "0.65", "0.70"])
    ax.tick_params(axis="x", length=3, pad=2, labelsize=fs, colors=CENIZA, labelcolor=TEXTO)
    for sp in ax.spines.values():
        sp.set_visible(False)
    ax.set_xlabel("AUROC, statement + Lean", fontsize=fs, labelpad=3, color=TEXTO)


def panel(fig, rect, m, fs, geom):
    ax = fig.add_axes(rect)
    R, W, dx, dy, alto = E.relieve(ax, m, fs=fs, **geom)
    ax.set_xlim(-13, W + (R - 1) * dx + 8)
    E.escala_vertical(ax, -2.4, alto, fs=fs - 1)
    E.flecha_capas(ax, W, R, dx, dy, fs=fs - 1)
    ytop = (R - 1) * dy + 2 * alto
    nom, _, wh, _ = E.MODELOS[m]
    ax.text(-12.5, ytop + 1, nom, color=wh, fontsize=fs + 2, weight="bold", va="top", ha="left")
    return ax


def cinco(presentes):
    ANCHO, fs = 12.0, 12.5
    nc, alto_cel, cab, pie = 3, 2.75, 0.75, 0.15
    nf = int(np.ceil(len(presentes) / nc))
    H = cab + nf * alto_cel + pie
    fig = plt.figure(figsize=(ANCHO, H))
    fig.text(0.012, 1 - 0.14 / H, "Where the separation is linearly readable: layer × position", fontsize=17, weight="bold",
             va="top", ha="left", color=TEXTO)
    w = ANCHO / nc
    for k, m in enumerate(presentes):
        f, c = divmod(k, nc)
        panel(fig, [(c * w + 0.05) / ANCHO, (H - cab - (f + 1) * alto_cel) / H, (w - 0.1) / ANCHO, (alto_cel - 0.05) / H],
              m, fs, E.GEOM3D)
    x0 = (2 * w + 0.45) / ANCHO                      # celda libre: clave y nota
    clave(fig, [x0, (pie + 2.12) / H, (w - 0.9) / ANCHO, 0.42 / H], presentes, fs - 1)
    fig.text(x0, (pie + 1.58) / H,
             "One slice per layer, the first in front.\nHeight and colour: out-of-fold AUROC of the\nlayer's probe direction at each position,\n"
             "450 CriticLeanBench formalizations.\nDark line: the Lean code alone.\nLightly smoothed along position; cells below\nchance sit on the baseline. Exploratory, one seed.",
             fontsize=fs - 1.5, color=CENIZA, va="top", ha="left", linespacing=1.3)
    os.makedirs(SALIDA, exist_ok=True)
    fig.savefig(os.path.join(SALIDA, "relieve_cinco_modelos.png")); plt.close(fig)


def uno(m):
    ANCHO, H, fs = 12.0, 6.6, 14.0
    fig = plt.figure(figsize=(ANCHO, H))
    ax = fig.add_axes([0.20, 0.03, 0.79, 0.86])
    R, W, dx, dy, alto = E.relieve(ax, m, dx=0.45, dy=1.6, alto=16.0, lw_borde=0.5, lw_fantasma=0.4, fs=fs)
    ax.set_xlim(-12, W + (R - 1) * dx + 8)
    E.escala_vertical(ax, -2.4, alto, fs=fs - 2)
    E.flecha_capas(ax, W, R, dx, dy, fs=fs - 2)
    nom, _, wh, _ = E.MODELOS[m]
    fig.text(0.02, 0.93, nom, color=wh, fontsize=28, weight="bold", va="center")
    fig.text(0.02, 0.855, "layer × position", color=CENIZA, fontsize=15, va="center")
    fig.text(0.02, 0.79, "One slice per layer,\nthe first in front.\n\nHeight and colour:\nout-of-fold AUROC of the\nlayer's probe direction,\n"
             "faithful vs. unfaithful\nLean 4 formalization,\nreading the statement\nand the Lean.\n\nDark line: the Lean code alone.\n\n"
             "Lightly smoothed along\nposition. Exploratory,\none seed.", color=CENIZA, fontsize=12, va="top", linespacing=1.3)
    os.makedirs(SALIDA, exist_ok=True)
    fig.savefig(os.path.join(SALIDA, f"relieve_{m}.png")); plt.close(fig)


if __name__ == "__main__":
    presentes = E.disponibles()
    cinco(presentes)
    uno(sys.argv[1] if len(sys.argv) > 1 else "qwen3_4b")
    print("escrito en", SALIDA, "->", sorted(os.listdir(SALIDA)))
