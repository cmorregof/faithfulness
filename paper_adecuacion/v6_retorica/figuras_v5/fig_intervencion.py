"""Figura de la intervención del Nivel B (S5), con la paleta y las reglas de color de figuras_v3.

Lee solo probes/intervencion/resultados_s5/tablas_nivel_b.json, que escribe tablas_nivel_b.py a partir de los
P(Yes) guardados (ninguna cifra está escrita a mano). Escribe, junto a este archivo, intervencion_nivel_b.pdf/.png
y su versión en español (sufijo _es).

Reglas de color (las de v3): color = identidad del modelo; gris ceniza = controles (direcciones al azar y la
dirección de lean_only); marcador lleno = estimación bajo una regla fijada de antemano; marcador hueco = post hoc
(Qwen3-4B, que además va en cursiva como modelo exploratorio).

Uso:  python3 figuras_v5/fig_intervencion.py      (TABLAS_S5=/ruta/tablas_nivel_b.json para otra ubicación)
Necesita matplotlib con LaTeX (lmodern, cm-super), tueplots y colorspacious, como figuras_v3.
"""
import json
import os
import sys

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.transforms import blended_transform_factory as blend

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import escaner_v3 as E   # noqa: E402  (paleta y rcParams: una sola fuente para todas las figuras)

TABLAS = os.environ.get("TABLAS_S5", os.path.join(AQUI, "..", "..", "..", "probes", "intervencion", "resultados_s5",
                                                  "tablas_nivel_b.json"))
TEXTO, CENIZA, GUIA, ANCHO = E.TEXTO, E.CENIZA, E.GUIA, E.ANCHO
plt.rcParams.update({"axes.spines.top": False, "axes.spines.right": False, "axes.grid": False,
                     "legend.frameon": False, "lines.solid_capstyle": "round"})
MS = ["olmo2_7b", "gemma3_4b", "llama31_8b", "qwen3_4b"]      # el orden del artículo en las figuras
PREVIA = {"olmo2_7b": True, "gemma3_4b": True, "llama31_8b": True, "qwen3_4b": False}   # ¿regla fijada de antemano?
tono = lambda m: E.MODELOS[m][2]
num = lambda x: r"$%+.3f$" % x
ic = lambda lo, hi: r"[$%+.3f$, $%+.3f$]" % (lo, hi)

TXT = {
    "en": dict(
        head=r"\textbf{Level B intervention} \textit{(mean over Lean tokens shifted toward the opposite class)}",
        probe="difference-of-means direction", rand="random direction (20)", lean="Lean-code-alone direction",
        col=r"drop $-$ random mean [95\% CI]", cnt=r"random $\geq$ direction", de="of",
        x1="drop in paired AUROC of P(Yes), 377 certified pairs",
        head2=r"\textbf{Larger shifts} \textit{(descriptive; 5 random directions)}",
        x2="shift, in distances between class means", y2="paired AUROC of P(Yes)", azar="chance",
        nota=r"filled: rule fixed in advance \quad open: post hoc"),
    "es": dict(
        head=r"\textbf{Intervención del Nivel B} \textit{(media sobre los tokens de Lean desplazada hacia la clase contraria)}",
        probe="dirección de diferencia de medias", rand="dirección al azar (20)", lean="dirección del código de Lean solo",
        col=r"caída $-$ media al azar [IC 95\%]", cnt=r"al azar $\geq$ dirección", de="de",
        x1="caída de la AUROC pareada de P(Yes), 377 pares certificados",
        head2=r"\textbf{Desplazamientos mayores} \textit{(descriptivo; 5 direcciones al azar)}",
        x2="desplazamiento, en distancias entre medias de clase", y2="AUROC pareada de P(Yes)", azar="azar",
        nota=r"lleno: regla fijada de antemano \quad hueco: post hoc"),
}


def marcador(ax, x, y, m, ms=4.8, **kw):
    ax.plot(x, y, "o", ms=ms, mfc=tono(m) if PREVIA[m] else "white", mec=tono(m), mew=1.0, **kw)


def figura(lang="en"):
    T = TXT[lang]
    S5 = json.load(open(TABLAS, encoding="utf-8"))["s5"]
    W, H = ANCHO, 4.05
    fig = plt.figure(figsize=(W, H))
    # ---------------------------------------------------------------- bloque 1: el criterio
    xl, xw = 1.18, 2.72
    a1 = fig.add_axes([xl / W, 2.52 / H, xw / W, 1.02 / H])
    T1 = blend(fig.transFigure, a1.transData)
    fig.text(0.012, 1 - 0.04 / H, T["head"], ha="left", va="top", fontsize=8.5)
    h = [plt.Line2D([], [], marker="|", ls="", ms=7, color=CENIZA, mew=0.9, alpha=0.75),
         plt.Line2D([], [], marker="D", ls="", ms=3.4, mfc="white", mec=CENIZA, mew=0.9),
         tuple(plt.Line2D([], [], marker="o", ls="", ms=4.6, mfc=tono(m) if PREVIA[m] else "white", mec=tono(m), mew=1.0)
               for m in MS)]
    from matplotlib.legend_handler import HandlerTuple
    fig.legend(handles=h, labels=[T["rand"], T["lean"], T["probe"]], loc="upper left",
               bbox_to_anchor=(0.012, 1 - 0.20 / H), ncol=3, handletextpad=0.4, columnspacing=1.2, handlelength=2.4,
               borderaxespad=0, fontsize=7.5, handler_map={tuple: HandlerTuple(ndivide=None, pad=0.1)})
    x_col, x_cnt = 5.46, 6.46
    a1.axvline(0, color=GUIA, lw=0.7, zorder=0.5)
    for i, m in enumerate(MS):
        d = S5[m]; p = d["f2"]
        a1.plot(p["caidas_azar"], [i] * len(p["caidas_azar"]), "|", ms=7, color=CENIZA, mew=0.9, alpha=0.75, zorder=2)
        a1.plot(d["solo_lean_f2_caida"], i, "D", ms=3.4, mfc="white", mec=CENIZA, mew=0.9, zorder=3)
        a1.plot(p["caida"][1:], [i, i], color=tono(m), lw=1.1, solid_capstyle="butt", zorder=4)
        marcador(a1, p["caida"][0], i, m, zorder=5)
        fig.text(0.012, i, E.nombre_tex(m), transform=T1, ha="left", va="center", fontsize=8, color=tono(m))
        fig.text(x_col / W, i, num(p["menos_azar"][0]) + r" \," + ic(*p["menos_azar"][1:]), transform=T1, ha="right",
                 va="center", fontsize=7.4, color=TEXTO)
        fig.text(x_cnt / W, i, r"$%d$ %s $%d$" % (p["n_azar_iguales_o_mayores"], T["de"], p["n_azar"]), transform=T1,
                 ha="right", va="center", fontsize=7.4, color=TEXTO if p["n_azar_iguales_o_mayores"] == 0 else CENIZA)
    fig.text(x_col / W, -0.95, T["col"], transform=T1, ha="right", va="center", fontsize=7, color=TEXTO)
    fig.text(x_cnt / W, -0.95, T["cnt"], transform=T1, ha="right", va="center", fontsize=7, color=TEXTO)
    a1.set_yticks([]); a1.spines["left"].set_visible(False)
    a1.set_ylim(len(MS) - 0.5, -0.6); a1.set_xlim(-0.33, 0.40)
    a1.set_xticks([-0.3, -0.2, -0.1, 0, 0.1, 0.2, 0.3, 0.4])
    a1.set_xticklabels([r"$-0.3$", r"$-0.2$", r"$-0.1$", "0", "0.1", "0.2", "0.3", "0.4"])
    a1.set_xlabel(T["x1"], labelpad=2)
    # ---------------------------------------------------------------- bloque 2: dosis
    fig.text(0.012, 1.86 / H, T["head2"], ha="left", va="top", fontsize=8.5)
    fig.text(1 - 0.006, 1.86 / H, T["nota"], ha="right", va="top", fontsize=7, color=CENIZA)
    X = [0, 1, 2, 4]
    pw, gap, x0 = 1.30, 0.22, 0.52
    for k, m in enumerate(MS):
        ax = fig.add_axes([(x0 + k * (pw + gap)) / W, 0.40 / H, pw / W, 1.10 / H])
        d = S5[m]; base = d["base"][0]
        ax.axhline(0.5, color=GUIA, lw=0.7, ls=(0, (2, 2)), zorder=0.5)
        for j in range(len(d["f4"]["auroc_azar"])):          # las 5 direcciones al azar que tienen las tres dosis
            ax.plot(X, [base, d["f2"]["auroc_azar"][j], d["f4"]["auroc_azar"][j], d["f8"]["auroc_azar"][j]],
                    color=CENIZA, lw=0.7, alpha=0.6, zorder=2)
        ys = [base, d["f2"]["auroc"], d["f4"]["auroc"], d["f8"]["auroc"]]
        ax.plot(X, ys, color=tono(m), lw=1.3, zorder=4)
        for x, f in zip(X[1:], ("f2", "f4", "f8")):
            ax.plot([x, x], d[f]["auroc_ic"], color=tono(m), lw=1.0, solid_capstyle="butt", zorder=4)
            marcador(ax, x, d[f]["auroc"], m, ms=4.2, zorder=5)
        ax.plot(0, base, "o", ms=3.6, mfc="white", mec=CENIZA, mew=0.9, zorder=5)
        ax.set_xlim(-0.3, 4.3); ax.set_ylim(0.05, 0.95)
        ax.set_xticks(X); ax.set_xticklabels(["0", r"$\times 1$", r"$\times 2$", r"$\times 4$"])
        ax.set_yticks([0.1, 0.3, 0.5, 0.7, 0.9])
        if k:
            ax.set_yticklabels([])
        else:
            ax.set_ylabel(T["y2"], labelpad=3)
        ax.set_title(E.nombre_tex(m), color=tono(m), fontsize=8, pad=3, loc="left")
        if k == len(MS) - 1:
            ax.text(4.25, 0.515, T["azar"], ha="right", va="bottom", fontsize=6.5, color=CENIZA)
    fig.text((x0 + (4 * pw + 3 * gap) / 2) / W, 0.03 / H, T["x2"], ha="center", va="bottom", fontsize=8.5)
    suf = "" if lang == "en" else "_es"
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(AQUI, f"intervencion_nivel_b{suf}.{ext}"))
    plt.close(fig)


if __name__ == "__main__":
    for lang in ("en", "es"):
        figura(lang)
    print("ok")
