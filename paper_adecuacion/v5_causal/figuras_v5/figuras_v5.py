"""figuras_v5.py — copia de v3_tmlr/figuras_v3.py (paquete_v3.tgz) con los rótulos «Lean code alone» /
«código de Lean solo» (13 nov 2026). Los datos y el dibujo no cambian. Escribe en v5_causal/figuras_v5/.
El bootstrap conjunto se lee de figuras/datos/bootstrap_conjunto.json (la ruta fuentes/posthoc_9nov/ no existe en el Mac).

Paper figures v3 (copy of figuras_v2/figuras_v2.py, modified): curves per model, Level A forest, Level B.

Run from anywhere:  python3 figuras_v3/figuras_v3.py
Writes, next to this file, English and Spanish versions (suffix _es) as PDF + PNG:
  curvas_por_modelo, forest_nivel_a, nivel_b
Reads only real data: ../figuras/datos/*.json and ../fuentes/*.json (and fuentes/posthoc_9nov/bootstrap_conjunto.json).
Needs: matplotlib >= 3.8 with LaTeX (lmodern, cm-super), tueplots, colorspacious.

v3 colour rule, shared with the scan (escaner_v3.py, which is the single source of the palette):
  * colour = model identity: each model carries its Wada hue in every figure (lines, points, names);
  * ash grey = baselines and controls (Lean alone, random weights, surface controls, P(Yes));
  * near-black = what the preregistered test reads (fixed layer, one-seed gap there, pooled estimates);
  * light tint of the model hue = the gap as an area or bar; neutral grey of the same lightness = negative gap.
Marker fill: filled = estimate under a rule written in advance (Level A and its controls); open = exploratory or
post hoc. Name style: upright = model of the preregistered replication, italic = exploratory model (constant per model).
"""
import json
import os
import sys

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.legend_handler import HandlerTuple
from matplotlib.patches import Patch
from matplotlib.transforms import blended_transform_factory as blend

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import escaner_v3 as E   # noqa: E402  (palette, ramps and rcParams: one source for every figure)

RAIZ = os.path.dirname(os.path.dirname(AQUI))   # paper_adecuacion/ (este guion vive en v5_causal/figuras_v5/)
DATOS = os.path.join(RAIZ, "figuras", "datos")
FUENTES = os.path.join(RAIZ, "fuentes")

TEXTO, CENIZA, GUIA = E.TEXTO, E.CENIZA, E.GUIA
NEGRO = TEXTO                      # near-black: what the preregistered test reads
ANCHO = E.ANCHO
plt.rcParams.update({"axes.spines.top": False, "axes.spines.right": False, "axes.grid": False,
                     "legend.frameon": False, "lines.solid_capstyle": "round"})

PRERREG = ["olmo2_7b", "gemma3_4b", "llama31_8b", "dsprover2_7b"]
EXPLOR = ["qwen3_4b", "goedel_8b", "kimina_7b", "qwen3_8b"]
assert all(E.MODELOS[m][3] for m in PRERREG) and not any(E.MODELOS[m][3] for m in EXPLOR)


def tono(m):
    return E.MODELOS[m][2]


def nombre(m):
    return E.nombre_tex(m)


def tinte(m, auroc=0.535):
    """Light tint of the model hue: the scan ramp at a fixed value (same lightness for every model)."""
    return E.rampa(m)((auroc - E.VMIN) / (E.VMAX - E.VMIN))[:3]


def gris_de(auroc=0.535):
    """Neutral grey with the same lightness as tinte(): used where the gap is negative (as in the scan's Delta map)."""
    J = float(E.J_de(auroc))
    return tuple(E.ucs_a_rgb(np.array([J]), np.array([0.0]), np.array([0.0]))[0])


def jl(*p):
    with open(os.path.join(*p)) as f:
        return json.load(f)


def guardar(fig, nombre_, lang):
    suf = "" if lang == "en" else "_es"
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(AQUI, f"{nombre_}{suf}.{ext}"))
    plt.close(fig)


def capa_fija(m):
    r = jl(FUENTES, f"v2_resultados_{m}.json")
    L = r["n_capas_mas_embeddings"] - 1
    assert r["capa_fija_lectura_ii"] == (2 * L) // 3
    return r["capa_fija_lectura_ii"], L


def num(x):
    return r"$%+.3f$" % x


def ic(lo, hi, signo=True):
    f = "%+.3f" if signo else "%.3f"
    return r"[$" + f % lo + r"$, $" + f % hi + r"$]"


TXT = {
    "en": dict(
        pre=r"\textbf{Preregistered replication}", exp=r"\textbf{Exploratory}",
        exp_curvas=r"\textbf{Exploratory} \textit{(not part of the decision rule)}",
        full="statement + Lean code (colour of the model)", lean="Lean code alone", gap="gap", gapneg="gap, Lean code alone above",
        fija=r"fixed layer $\lfloor 2L/3\rfloor$", gapfija="one-seed gap there",
        xcurvas=r"relative depth $\ell/L$ \;(0 = embeddings, 1 = last block);\; AUROC axis starts at chance, 0.5",
        joint="Mean of the four, joint bootstrap", dl=r"Pooled, pre-specified (DerSimonian--Laird)",
        ctl=r"\textbf{Control}", rw="Qwen3-4B, random weights", col=r"$\Delta$ \; [95\% CI]",
        xforest=r"$\Delta$ AUROC = (statement + Lean code) $-$ (Lean code alone), fixed layer $\lfloor 2L/3\rfloor$",
        bhead=r"\textbf{Level B} \textit{(exploratory; rule approved before the analysis)}",
        bfull="statement + Lean code", blean="Lean code alone", bgap="gap (tested)",
        cs="cross-surface control", ng="n-gram control (both texts)",
        colgap=r"gap [95\% CI]", colpy=r"P(Yes) [95\% CI]",
        xb="paired AUROC, 377 certified pairs",
        fhead=r"\textbf{Qwen3-4B by edit family} \textit{(post hoc)}",
        fam=["A stronger", "B weaker", "C (all)", "C2 numeral", "C3 other"],
        coldif=r"difference [95\% CI]",
        xf=r"(statement + Lean code) $-$ cross-surface control",
    ),
    "es": dict(
        pre=r"\textbf{Réplica prerregistrada}", exp=r"\textbf{Exploratorio}",
        exp_curvas=r"\textbf{Exploratorio} \textit{(fuera de la regla de decisión)}",
        full="enunciado + código de Lean (color del modelo)", lean="código de Lean solo", gap="brecha", gapneg="brecha, código de Lean solo por encima",
        fija=r"capa fija $\lfloor 2L/3\rfloor$", gapfija="brecha de una semilla en esa capa",
        xcurvas=r"profundidad relativa $\ell/L$ \;(0 = embeddings, 1 = último bloque);\; el eje de AUROC empieza en el azar, 0.5",
        joint="Media de los cuatro, bootstrap conjunto", dl=r"Combinado, prerregistrado (DerSimonian--Laird)",
        ctl=r"\textbf{Control}", rw="Qwen3-4B, pesos aleatorios", col=r"$\Delta$ \; [IC 95\%]",
        xforest=r"$\Delta$ AUROC = (enunciado + código de Lean) $-$ (código de Lean solo), capa fija $\lfloor 2L/3\rfloor$",
        bhead=r"\textbf{Nivel B} \textit{(exploratorio; regla aprobada antes del análisis)}",
        bfull="enunciado + código de Lean", blean="código de Lean solo", bgap="brecha (puesta a prueba)",
        cs="control de superficie cruzada", ng="control de n-gramas (ambos textos)",
        colgap=r"brecha [IC 95\%]", colpy=r"P(Yes) [IC 95\%]",
        xb="AUROC pareada, 377 pares certificados",
        fhead=r"\textbf{Qwen3-4B por familia de edición} \textit{(post hoc)}",
        fam=["A más fuerte", "B más débil", "C (todas)", "C2 numeral", "C3 otra"],
        coldif=r"diferencia [IC 95\%]",
        xf=r"(enunciado + código de Lean) $-$ control de superficie cruzada",
    ),
}


# ----------------------------------------------------------------------------------------------
# (i) one curve per model: small multiples
# ----------------------------------------------------------------------------------------------
def fig_curvas(lang="en"):
    T = TXT[lang]
    fig, axs = plt.subplots(2, 4, figsize=(ANCHO, 3.95), sharex=True, sharey=True,
                            gridspec_kw={"hspace": 0.50, "wspace": 0.10})
    fig.subplots_adjust(left=0.075, right=0.985, top=0.805, bottom=0.105)
    negativo = False
    for i, m in enumerate(PRERREG + EXPLOR):
        ax = axs.flat[i]
        d = jl(DATOS, f"curvas_{m}_media_lean.json")["curvas"]
        c, s = np.array(d["completo"]), np.array(d["solo_lean"])
        k, L = capa_fija(m)
        x = np.arange(len(c)) / L
        ax.fill_between(x, s, c, where=c >= s, interpolate=True, color=tinte(m), lw=0, zorder=1)
        if np.any(c < s):
            negativo = True
            ax.fill_between(x, s, c, where=c < s, interpolate=True, color=gris_de(), lw=0, zorder=1)
        ax.plot(x, s, color=CENIZA, lw=0.85, zorder=2)
        ax.plot(x, c, color=tono(m), lw=1.25, zorder=3)
        # the preregistered readout: dotted near-black rule at floor(2L/3), the one-seed gap there drawn solid
        ax.axvline(k / L, color=NEGRO, lw=0.6, ls=(0, (1, 1.6)), zorder=1.5)
        ax.plot([k / L, k / L], [s[k], c[k]], color=NEGRO, lw=1.6, solid_capstyle="butt", zorder=4)
        ax.set_title(nombre(m), loc="left", pad=3, fontsize=8, color=tono(m))
        ax.text(0.97, 0.05, f"$L={L}$", transform=ax.transAxes, ha="right", va="bottom", fontsize=7, color=CENIZA)
        ax.set_ylim(0.50, 0.80); ax.set_xlim(0, 1)
        ax.set_yticks([0.5, 0.6, 0.7, 0.8]); ax.set_yticklabels(["0.5", "0.6", "0.7", "0.8"])
        ax.set_xticks([0, 0.5, 1]); ax.set_xticklabels(["0", "0.5", "1"])
    for ax in axs[:, 0]:
        ax.set_ylabel("AUROC")
    fig.supxlabel(T["xcurvas"], y=0.010, fontsize=8.5)
    p0, p1 = axs[0, 0].get_position(), axs[1, 0].get_position()
    fig.text(0.012, p0.y1 + 0.052, T["pre"], ha="left", va="bottom", fontsize=8.5)
    fig.text(0.012, p1.y1 + 0.052, T["exp_curvas"], ha="left", va="bottom", fontsize=8.5)
    # key: two rows above the panels; every mark drawn in the figure has an entry
    hues = [tono(m) for m in PRERREG[:3]]
    h_full = tuple(plt.Line2D([], [], color=h, lw=1.25) for h in hues)
    h_gap = tuple(Patch(color=tinte(m), lw=0) for m in PRERREG[:3])
    h = [h_full, plt.Line2D([], [], color=CENIZA, lw=0.85), h_gap,
         plt.Line2D([], [], color=NEGRO, lw=0.8, ls=(0, (1, 1.6))),
         plt.Line2D([], [], color=NEGRO, lw=1.6, solid_capstyle="butt"), Patch(color=gris_de(), lw=0)]
    lab = [T["full"], T["lean"], T["gap"], T["fija"], T["gapfija"], T["gapneg"]]
    if not negativo:
        h, lab = h[:-1], lab[:-1]
    fig.legend(handles=h, labels=lab, loc="lower left", bbox_to_anchor=(0.012, 0.885), ncol=3,
               handlelength=2.2, columnspacing=1.4, handletextpad=0.5, borderaxespad=0, fontsize=7.5,
               handler_map={tuple: HandlerTuple(ndivide=None, pad=0.0)})
    guardar(fig, "curvas_por_modelo", lang)


# ----------------------------------------------------------------------------------------------
# (ii) Level A forest plot, readout (ii)
# ----------------------------------------------------------------------------------------------
def fig_forest(lang="en"):
    T = TXT[lang]
    L = "ii_media_lean_capa_fija"
    meta = jl(FUENTES, "v2_metaanalisis.json")[L]
    conj = jl(DATOS, "bootstrap_conjunto.json")[L]
    filas = [("cab", T["pre"], None, None, None)]
    for m in PRERREG:
        r = jl(FUENTES, f"v2_resultados_{m}.json")["lecturas"][L]
        filas.append(("pre", m, r["delta"], r["ic_delta"], None))
    # the four per-model deltas behind the joint bootstrap must be the ones drawn above
    assert np.allclose(conj["deltas"], [round(jl(FUENTES, f"v2_resultados_{m}.json")["lecturas"][L]["delta"], 4) for m in PRERREG], atol=1e-4)
    filas.append(("joint", T["joint"], conj["media"], conj["ic95"], None))
    filas.append(("dl", T["dl"], meta["estimacion"], meta["ic"], None))
    filas.append(("gap", None, None, None, None))
    filas.append(("cab", T["exp"], None, None, None))
    for m in EXPLOR:
        r = jl(FUENTES, f"v2_resultados_{m}.json")["lecturas"][L]
        filas.append(("exp", m, r["delta"], r["ic_delta"], None))
    filas.append(("gap", None, None, None, None))
    filas.append(("cab", T["ctl"], None, None, None))
    r = jl(FUENTES, "v2_resultados_qwen3_4b_aleatorio.json")["lecturas"][L]
    filas.append(("ctl", T["rw"], r["delta"], r["ic_delta"], None))

    alto = {"cab": 0.95, "gap": 0.35}
    ys, y = [], 0.0
    for f in filas:
        ys.append(y); y += alto.get(f[0], 1.0)
    fig, ax = plt.subplots(figsize=(ANCHO, 3.30))
    fig.subplots_adjust(left=0.375, right=0.765, top=0.985, bottom=0.125)
    Tr = blend(fig.transFigure, ax.transData)
    ax.axvline(0, color=GUIA, lw=0.6, zorder=0.5)
    for (kind, lab, d, ci, _), yy in zip(filas, ys):
        if kind == "gap":
            continue
        if kind == "cab":
            fig.text(0.015, yy, lab, transform=Tr, ha="left", va="center", fontsize=8)
            continue
        if kind in ("pre", "exp"):
            fig.text(0.035, yy, nombre(lab), transform=Tr, ha="left", va="center", fontsize=8, color=tono(lab))
        else:
            fig.text(0.035, yy, lab, transform=Tr, ha="left", va="center", fontsize=8, color=TEXTO)
        txt = num(d) + r" \; " + ic(*ci)
        fig.text(0.995, yy, txt, transform=Tr, ha="right", va="center", fontsize=7.6, color=TEXTO)
        if kind in ("joint", "dl"):
            xs_, ys_ = [ci[0], d, ci[1], d], [yy, yy - 0.30, yy, yy + 0.30]
            if kind == "joint":
                ax.fill(xs_, ys_, color=NEGRO, lw=0, zorder=3)
            else:
                ax.fill(xs_, ys_, facecolor="white", edgecolor=NEGRO, lw=0.9, zorder=3)
            continue
        col = CENIZA if kind == "ctl" else tono(lab)
        ax.plot(ci, [yy, yy], color=col, lw=1.0, zorder=2, solid_capstyle="butt")
        ax.plot(d, yy, "o", ms=4.6, mew=1.0, mec=col, mfc="white" if kind == "exp" else col, zorder=3)
    fig.text(0.995, ys[0], T["col"], transform=Tr, ha="right", va="center", fontsize=7.6, color=CENIZA)
    ax.set_ylim(ys[-1] + 0.6, ys[0] - 0.6)
    ax.set_yticks([]); ax.spines["left"].set_visible(False)
    ax.set_xlim(-0.145, 0.145); ax.set_xticks([-0.10, -0.05, 0, 0.05, 0.10])
    ax.set_xticklabels([r"$-0.10$", r"$-0.05$", "0", r"$0.05$", r"$0.10$"])
    ax.set_xlabel(T["xforest"], x=0.62)
    guardar(fig, "forest_nivel_a", lang)


# ----------------------------------------------------------------------------------------------
# (iii) Level B: paired comparison (top) + post hoc family breakdown in Qwen3-4B (bottom)
# ----------------------------------------------------------------------------------------------
FAMILIAS_QWEN = [  # fuentes/superficie_cruzada_por_familia.md (post hoc, Qwen3-4B): completo - cruzada
    (0.082, -0.038, 0.195, 142, 0),
    (0.098, 0.000, 0.195, 136, 0),
    (0.098, 0.006, 0.188, 99, 0),
    (-0.020, -0.103, 0.056, 68, 1),
    (0.385, 0.192, 0.577, 31, 1),
]


def fig_nivel_b(lang="en"):
    T = TXT[lang]
    ms = ["olmo2_7b", "gemma3_4b", "llama31_8b", "qwen3_4b"]          # the paper's model order, as everywhere
    B = {m: jl(FUENTES, f"nivel_b_{m}_principal.json") for m in ms}
    cruz = B[ms[0]]["secundarios"]["superficie_cruzada"]["cruzada"]
    ngr = B[ms[0]]["secundarios"]["superficie"]["superficie"]
    for m in ms:   # both surface controls are model-free: the same numbers in every file
        assert np.allclose(B[m]["secundarios"]["superficie_cruzada"]["cruzada"], cruz)
        assert np.allclose(B[m]["secundarios"]["superficie"]["superficie"], ngr)
    W, H = ANCHO, 3.78
    fig = plt.figure(figsize=(W, H))
    xl, xw = 1.18, 2.30                                     # inches: axes left edge and width (both rows)
    x_gap, x_py, x_n = 4.72, 6.46, 5.30                     # right edges of the number columns (inches)
    a1 = fig.add_axes([xl / W, 2.08 / H, xw / W, 1.26 / H])
    a2 = fig.add_axes([xl / W, 0.34 / H, xw / W, 1.08 / H])
    T1 = blend(fig.transFigure, a1.transData)
    fig.text(0.012, 1 - 0.04 / H, T["bhead"], ha="left", va="top", fontsize=8.5)
    # key (top right)
    h = [plt.Line2D([], [], marker="o", ls="", ms=4.6, mfc="white", mec=CENIZA, mew=1.0),
         tuple(plt.Line2D([], [], marker="o", ls="", ms=4.6, mfc="white", mec=tono(m), mew=1.0) for m in ms[:3]),
         tuple(plt.Line2D([], [], color=tinte(m, 0.60), lw=3.0, solid_capstyle="butt") for m in ms[:3])]
    fig.legend(handles=h, labels=[T["blean"], T["bfull"], T["bgap"]], loc="upper right",
               bbox_to_anchor=(0.995, 1 - 0.20 / H), ncol=3, handletextpad=0.4, columnspacing=1.0, handlelength=2.0,
               borderaxespad=0, fontsize=7.5, handler_map={tuple: HandlerTuple(ndivide=None, pad=0.1)})
    # surface controls: one vertical line each (model-free), interval drawn once as a whisker above the rows
    for v, ls, yk, lab in ((cruz, (0, (3, 2)), -1.55, T["cs"]), (ngr, (0, (1, 1.5)), -0.85, T["ng"])):
        a1.plot([v[0], v[0]], [yk, len(ms) - 0.5], color=CENIZA, lw=0.7, ls=ls, zorder=0.5)
        a1.plot([v[1], v[2]], [yk, yk], color=CENIZA, lw=0.8, solid_capstyle="butt", zorder=0.5)
        a1.text(v[1] - 0.006, yk, lab, ha="right", va="center", fontsize=6.8, color=CENIZA)
    for i, m in enumerate(ms):
        c, l = B[m]["central"]["completo"], B[m]["central"]["solo_lean"]
        dif = B[m]["central"]["diferencia"]
        py = B[m]["secundarios"]["p_yes"]["p_yes"]
        a1.plot([l[0], c[0]], [i, i], color=tinte(m, 0.60), lw=3.0, solid_capstyle="butt", zorder=2)
        a1.plot(l[0], i, "o", ms=4.6, mfc="white", mec=CENIZA, mew=1.0, zorder=3)
        a1.plot(c[0], i, "o", ms=4.6, mfc="white", mec=tono(m), mew=1.0, zorder=3)
        fig.text(0.012, i, nombre(m), transform=T1, ha="left", va="center", fontsize=8, color=tono(m))
        fig.text(x_gap / W, i, num(dif[0]) + r" \," + ic(dif[1], dif[2]), transform=T1, ha="right", va="center",
                 fontsize=7.4, color=TEXTO)
        fig.text(x_py / W, i, r"$%.3f$ \," % py[0] + ic(py[1], py[2], signo=False), transform=T1, ha="right",
                 va="center", fontsize=7.4, color=CENIZA)
    fig.text(x_gap / W, -1.55, T["colgap"], transform=T1, ha="right", va="center", fontsize=7, color=TEXTO)
    fig.text(x_py / W, -1.55, T["colpy"], transform=T1, ha="right", va="center", fontsize=7, color=CENIZA)
    a1.set_yticks([]); a1.spines["left"].set_visible(False)
    a1.set_ylim(len(ms) - 0.5, -1.85); a1.set_xlim(0.50, 0.85)
    a1.set_xticks([0.5, 0.6, 0.7, 0.8]); a1.set_xticklabels(["0.5", "0.6", "0.7", "0.8"])
    a1.set_xlabel(T["xb"], labelpad=2)
    # bottom: post hoc, Qwen3-4B by edit family (open markers: post hoc)
    T2 = blend(fig.transFigure, a2.transData)
    fig.text(0.012, 1.50 / H, T["fhead"], ha="left", va="bottom", fontsize=8.5)
    a2.axvline(0, color=GUIA, lw=0.6, zorder=0)
    ys = [0, 1, 2, 3, 4]
    q = "qwen3_4b"
    for (d, lo, hi, n, sub), y, lab in zip(FAMILIAS_QWEN, ys, T["fam"]):
        a2.plot([lo, hi], [y, y], color=tono(q), lw=0.9, solid_capstyle="butt")
        a2.plot(d, y, "o", ms=4.2, mfc="white", mec=tono(q), mew=1.0)
        fig.text(0.012 + 0.022 * sub, y, lab, transform=T2, ha="left", va="center", fontsize=7.8,
                 color=TEXTO if not sub else CENIZA)
        fig.text(x_gap / W, y, num(d) + r" \," + ic(lo, hi), transform=T2, ha="right", va="center", fontsize=7.4, color=TEXTO)
        fig.text(x_n / W, y, f"$n={n}$", transform=T2, ha="right", va="center", fontsize=7.4, color=CENIZA)
    fig.text(x_gap / W, -0.95, T["coldif"], transform=T2, ha="right", va="center", fontsize=7, color=TEXTO)
    a2.set_yticks([]); a2.spines["left"].set_visible(False)
    a2.set_ylim(ys[-1] + 0.5, -1.2); a2.set_xlim(-0.15, 0.62); a2.set_xticks([0, 0.2, 0.4, 0.6])
    a2.set_xticklabels(["0", "0.2", "0.4", "0.6"])
    a2.set_xlabel(T["xf"], labelpad=2)
    guardar(fig, "nivel_b", lang)


if __name__ == "__main__":
    for lang in ("en", "es"):
        fig_curvas(lang); fig_forest(lang); fig_nivel_b(lang)
    print("negative-gap grey", gris_de(), "tint J", float(E.J_de(0.535)))
