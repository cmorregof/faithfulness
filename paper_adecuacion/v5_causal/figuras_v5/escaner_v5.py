#!/usr/bin/env python3
"""escaner_v5.py — la figura de los mapas (fig:escaner) rehecha para leerse mejor (13 nov 2026).

Mismos datos, mismas rampas y mismos tres paneles que escaner_v3.py, del que importa la paleta, las rampas y la
carga de datos. Cambia solo la disposición:
  - figura de página completa: filas de mapa más altas y columnas un 15 % más anchas;
  - el nombre del modelo va encima de su fila, y el margen izquierdo queda para el eje de capas;
  - ningún texto baja de 8 pt (antes iban de 6.8 a 8.5 pt);
  - la nota de cuatro líneas al pie desaparece. Lo que no repite el pie de figura pasa a los rótulos: qué es Q/P
    (pregunta; la última columna es el último token) y el tamaño del ruido de una celda (0.5 ± 0.045).
Las celdas siguen crudas, una por píxel lógico, sin suavizar.

Lee figuras_v5/escaner_out/mapa_<modelo>.npz (los escribe mapas_desde_escaner.py) y escribe
figuras_v5/escaner2d_modelos_v5.{pdf,png} y escaner2d_modelos_v5_es.{pdf,png}.
Necesita numpy, matplotlib, colorspacious y tueplots (este último solo porque escaner_v3.py lo importa). No usa
LaTeX: el texto va en Latin Modern desde los .otf de TeX Live, así que no hacen falta cm-super ni dvipng.
Uso:  <python> escaner_v5.py
"""
import glob
import os

AQUI = os.path.dirname(os.path.abspath(__file__))
os.environ.setdefault("ESCANER_DATOS", os.path.join(AQUI, "escaner_out"))
os.environ.setdefault("ESCANER_SALIDA", AQUI)

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager as fm

import escaner_v3 as E

for f in glob.glob("/usr/local/texlive/*/texmf-dist/fonts/opentype/public/lm/lmroman10-*.otf"):
    fm.fontManager.addfont(f)
plt.rcParams.update({
    "text.usetex": False, "font.family": "serif", "font.serif": ["Latin Modern Roman", "DejaVu Serif"],
    "mathtext.fontset": "cm", "font.size": 9, "pdf.fonttype": 3,   # 3: con .otf (CFF) el tipo 42 queda mal incrustado
    "savefig.dpi": 300,
    "axes.linewidth": 0.5, "xtick.major.width": 0.5, "ytick.major.width": 0.5,
})
TEXTO, CENIZA = E.TEXTO, E.CENIZA
ANCHO = 6.5
MIN = 8.0          # ningún texto por debajo de este cuerpo

TXT = {
    "en": dict(
        tit=["statement + Lean", "Lean code alone", r"difference $\Delta$"],
        tramo={"statement": "statement", "Lean": "Lean", "question": "Q"},
        q="Q = question tokens; the last column is the last token",
        pre="Level A replication models", exp="Other models", capa="layer",
        clave_a="out-of-fold AUROC (grey: below chance)",
        clave_d=r"$\Delta$ = (statement + Lean) $-$ (Lean code alone)",
        ruido=r"one cell, permuted labels, 5–95%%: $0.5 \pm %.3f$" % E.PISO,
        ruido_d="same, if independent",
    ),
    "es": dict(
        tit=["enunciado + Lean", "código de Lean solo", r"diferencia $\Delta$"],
        tramo={"statement": "enunciado", "Lean": "Lean", "question": "P"},
        q="P = tokens de la pregunta; la última columna es el último token",
        pre="Modelos de la réplica del Nivel A", exp="Otros modelos", capa="capa",
        clave_a="AUROC fuera de pliegue (gris: bajo el azar)",
        clave_d=r"$\Delta$ = (enunciado + Lean) $-$ (código de Lean solo)",
        ruido=r"una celda, etiquetas permutadas, 5–95 %%: $0.5 \pm %.3f$" % E.PISO,
        ruido_d="igual, si fueran independientes",
    ),
}


def fig_2d(presentes, lang="en"):
    T = TXT[lang]
    n = len(presentes)
    TA, TB = E.TRAMOS, E.TRAMOS[3:]
    _, WA = E.posiciones(TA)
    _, WB = E.posiciones(TB)
    sep = 7.0
    izq, der = 0.40, 0.04                               # pulgadas
    unidad = (ANCHO - izq - der) / (WA + 2 * WB + 2 * sep)
    alto_fila, nombre_h, hueco_fila = 0.78, 0.18, 0.06
    cab = 0.21                                          # línea de encabezado de grupo
    grupos = [m for k, m in enumerate(presentes) if k == 0 or E.MODELOS[m][3] != E.MODELOS[presentes[k - 1]][3]]
    paso = 0.075                                        # alto de cada tira de la clave
    kh = paso * n
    ky = 0.36                                           # base de las claves
    arriba = 0.24                                       # títulos de columna
    tramo_h, q_h = 0.19, 0.17                           # rótulos de tramo bajo la última fila y línea que explica Q
    abajo = ky + kh + 0.27 + 0.10 + q_h + tramo_h
    H = arriba + n * (alto_fila + nombre_h) + (n - 1) * hueco_fila + len(grupos) * cab + abajo
    fig = plt.figure(figsize=(ANCHO, H))
    xs = [izq, izq + (WA + sep) * unidad, izq + (WA + WB + 2 * sep) * unidad]
    ws = [WA * unidad, WB * unidad, WB * unidad]
    for k in range(3):                                  # títulos de columna, una vez, arriba
        fig.text(xs[k] / ANCHO, (H - 0.05) / H, T["tit"][k], fontsize=10, va="top", ha="left", color=TEXTO)
    cursor = H - arriba
    for i, m in enumerate(presentes):
        nom, _, wh, pre = E.MODELOS[m]
        if m in grupos:
            cursor -= cab
            fig.text(0.006, (cursor + 0.05) / H, T["pre"] if pre else T["exp"], fontsize=9.5, weight="bold",
                     va="bottom", ha="left", color=TEXTO)
        c, s, d = E.cargar(m)
        R = c.shape[0]
        cursor -= nombre_h
        fig.text(xs[0] / ANCHO, (cursor + 0.045) / H, nom, color=wh, fontsize=10, weight="bold",
                 style="normal" if pre else "italic", va="bottom", ha="left")
        y = cursor - alto_fila
        cm, dv = E.rampa_v3(m), E.divergente(m)
        f = E.capa_fija(R)
        for k, (Z, tr, mapa, lo, hi) in enumerate(((c, TA, cm, E.VMIN_BAJO, E.VMAX), (s, TB, cm, E.VMIN_BAJO, E.VMAX),
                                                   (d, TB, dv, -E.DMAX, E.DMAX))):
            ax = fig.add_axes([xs[k] / ANCHO, y / H, ws[k] / ANCHO, alto_fila / H])
            pos, W = E.dibujar_tramos(ax, Z, tr, mapa, lo, hi)
            ax.plot([-1.6], [f + 0.5], marker=">", ms=4.6, color=TEXTO, clip_on=False, mew=0)
            if k == 0:
                ax.set_yticks([0.5, R - 0.5]); ax.set_yticklabels(["0", str(R - 1)])
                ax.tick_params(axis="y", length=2, pad=4.5, labelsize=MIN, colors=CENIZA, labelcolor=TEXTO)
                ax.set_ylabel(T["capa"], fontsize=MIN, labelpad=-3, color=TEXTO)
            if i == n - 1:
                for nomt, a, b, x0 in pos:
                    if nomt in T["tramo"]:
                        ax.text(x0 + (b - a) / 2, -0.07 * R, T["tramo"][nomt], ha="center", va="top", fontsize=9, color=TEXTO)
        cursor = y - hueco_fila
    fig.text(xs[0] / ANCHO, (ky + kh + 0.27 + 0.10) / H, T["q"], fontsize=MIN, color=CENIZA, va="bottom", ha="left")

    def clave(x0, w, mapas, lo, hi, ticks, fmt, etiqueta, piso, txt_piso):
        top = ky + kh
        for j, mp in enumerate(mapas):
            a = fig.add_axes([x0 / ANCHO, (top - (j + 1) * paso + 0.008) / H, w / ANCHO, (paso - 0.008) / H])
            a.imshow(np.linspace(0, 1, 512)[None], aspect="auto", cmap=mp, extent=(lo, hi, 0, 1))
            a.set_xlim(lo, hi); a.set_yticks([])
            for sp in a.spines.values():
                sp.set_visible(False)
            if j < len(mapas) - 1:
                a.set_xticks([])
        a.set_xticks(ticks); a.set_xticklabels([fmt(t) for t in ticks])
        a.tick_params(axis="x", length=2.5, pad=2, labelsize=MIN, colors=CENIZA, labelcolor=TEXTO)
        a.set_xlabel(etiqueta, fontsize=9, labelpad=2.5, color=TEXTO)
        ab = fig.add_axes([x0 / ANCHO, (top + 0.015) / H, w / ANCHO, 0.24 / H])   # corchete de ruido sobre la clave
        ab.set_xlim(lo, hi); ab.set_ylim(0, 1); ab.axis("off")
        c0 = 0.5 if lo > 0 else 0.0
        ab.plot([c0 - piso, c0 - piso, c0 + piso, c0 + piso], [0.03, 0.30, 0.30, 0.03], color=TEXTO, lw=0.7, solid_joinstyle="miter")
        ab.text(c0, 0.42, txt_piso, ha="center", va="bottom", fontsize=MIN, color=TEXTO)

    def fmt_d(t):
        return ("−" if t < 0 else ("+" if t > 0 else "")) + f"{abs(t):.2f}"
    clave(xs[0] + 0.10 * ws[0], 0.80 * ws[0], [E.rampa_v3(m) for m in presentes], E.VMIN_BAJO, E.VMAX,
          [0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7], lambda t: f"{t:.2f}", T["clave_a"], E.PISO, T["ruido"])
    clave(xs[1] + 0.25 * ws[1], ws[2] + sep * unidad + 0.75 * ws[1] - 0.16, [E.divergente(m) for m in presentes], -E.DMAX, E.DMAX,
          [-0.12, -0.06, 0, 0.06, 0.12], fmt_d, T["clave_d"], E.PISO_DIF, T["ruido_d"])
    E.SALIDA = os.environ["ESCANER_SALIDA"]
    E.guardar(fig, "escaner2d_modelos_v5" + ("" if lang == "en" else "_es"))
    return H


if __name__ == "__main__":
    presentes = E.disponibles()
    print("modelos:", presentes)
    for lang in ("en", "es"):
        print(lang, "alto de la figura: %.2f in" % fig_2d(presentes, lang))
