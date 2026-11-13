"""Scan figures v3 (copy of diseno/escaner_diseno.py, modified): one Wada colour per model, equal lightness at
equal AUROC; v3 adds a grey arm below chance, the noise floor of one cell, group headings and Spanish labels.

Run from /home/claude/paper:   python3 figuras_v3/escaner_v3.py        (2D scan, English + Spanish)
                               python3 figuras_v3/escaner_v3.py todo   (also swatch sheet and 3D relief)
This module is also the single source of the model palette for figuras_v3.py.
Reads every escaner_out/mapa_<model>.npz that exists (arrays "completo" and "solo_lean", rows = layers, bottom row =
first layer; 92 columns = 2 | 40 statement | 2 | 40 Lean | 8 question) and writes, into diseno/:
  paleta_rampas.{pdf,png}       swatch sheet of the final ramps with their Wada names
  escaner2d_modelos.{pdf,png}   2D scan: statement+Lean | Lean alone | difference, one row per model (raw cells)
  escaner3d_modelos.{pdf,png}   relief of every model, layer slices, Lean-alone line drawn on each slice
  escaner3d_heroe_qwen3_4b.{pdf,png}   single-model opening image (repository / talk)
  comprobaciones.json           numeric checks of the ramps (lightness, CVD, gamut)
Needs matplotlib + LaTeX (lmodern, cm-super), colorspacious, tueplots.
"""
import glob
import json
import os

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.collections import PolyCollection
from matplotlib.colors import ListedColormap, to_rgb
from colorspacious import cspace_convert
from tueplots import bundles

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(AQUI)
DATOS = os.environ.get("ESCANER_DATOS", os.path.join(RAIZ, "escaner_out"))

# ------------------------------------------------------------------------------------------------
# 1. Palette. Hues are taken from real colours in Sanzo Wada, "A Dictionary of Colour Combinations"
#    (machine-readable copy: github.com/mattdesl/dictionary-of-colour-combinations, colors.json,
#    saved here as wada_colors.json). "con" = a Wada combination that pairs it with a colour of 214.
# ------------------------------------------------------------------------------------------------
TEXTO, CENIZA, GUIA = "#24212B", "#6E6878", "#B9B4C0"
MODELOS = {   # key: (display name, Wada name, Wada hex, preregistered?)
    "olmo2_7b":     ("OLMo-2-7B",             "Cossack Green",       "#437742", True),
    "gemma3_4b":    ("Gemma-3-4B",            "Sudan Brown",         "#A36752", True),
    "llama31_8b":   ("Llama-3.1-8B",          "Pansy Purple",        "#7D133A", True),
    "dsprover2_7b": ("DeepSeek-Prover-V2-7B", "Dusky Green",         "#004F46", True),
    "qwen3_4b":     ("Qwen3-4B",              "Violet",              "#4F4086", False),
    "goedel_8b":    ("Goedel-Prover-V2-8B",   "Aconite Violet",      "#A36AA5", False),
    "kimina_7b":    ("Kimina-7B",             "Deep Grayish Olive",  "#635A3A", False),
    "qwen3_8b":     ("Qwen3-8B",              "Vandar Poel's Blue",  "#064F6E", False),
}
ORDEN = list(MODELOS)
COMBO = {"olmo2_7b": "262 + Ivory Buff", "gemma3_4b": "214", "llama31_8b": "273 + Sudan Brown",
         "dsprover2_7b": "94 + Ivory Buff", "qwen3_4b": "214", "goedel_8b": "301 + Ivory Buff",
         "kimina_7b": "343 + Ivory Buff", "qwen3_8b": "343 + Ivory Buff"}          # preregistered first, then exploratory: the paper's order everywhere

# Ramp geometry (CAM02-UCS). Lightness J' is the same linear function of the value for every model;
# only the hue angle differs. Chroma follows one shared, sober envelope (peak 20, below Wada's Violet, 23).
VMIN, VMAX = 0.50, 0.70        # AUROC: chance -> highest value seen (0.689)
J_CLARO, J_OSCURO = 96.0, 24.0 # light end (chance, a tinted paper) and dark end
C_PICO, J_PICO = 18.5, 46.0    # chroma peak (sober: below Wada Violet, 23) and the lightness where it sits
C_CLARO, C_OSCURO = 2.5, 13.0  # chroma at the two ends
DMAX = 0.12                    # difference map: symmetric limits, values beyond are clipped (counted below)
J_CENTRO = 97.5                # difference map: neutral centre
H_CENIZA = 291.1               # hue of ash grey #6E6878 in CAM02-UCS; negative arm of the difference map
C_CENIZA = 6.0


def ucs(hexa):
    return cspace_convert(np.array(to_rgb(hexa)), "sRGB1", "CAM02-UCS")


def tono(hexa):
    J, a, b = ucs(hexa)
    return float(np.degrees(np.arctan2(b, a)) % 360)


def croma(J):
    """Shared chroma envelope as a function of lightness: rises from the dark end to the peak, falls to the light end."""
    J = np.asarray(J, float)
    sub = C_OSCURO + (C_PICO - C_OSCURO) * np.sin(0.5 * np.pi * np.clip((J - J_OSCURO) / (J_PICO - J_OSCURO), 0, 1))
    baja = C_CLARO + (C_PICO - C_CLARO) * np.cos(0.5 * np.pi * np.clip((J - J_PICO) / (J_CLARO - J_PICO), 0, 1)) ** 1.3
    return np.where(J <= J_PICO, sub, baja)


_G = np.linspace(0, 1, 2001)
_GU = cspace_convert(np.stack([_G, _G, _G], 1), "sRGB1", "CAM02-UCS")   # sRGB greys in CAM02-UCS


def neutro_ab(J):
    """a', b' of the sRGB-neutral grey with lightness J' (CAM02-UCS greys are not exactly at a' = b' = 0)."""
    return np.interp(J, _GU[:, 0], _GU[:, 1]), np.interp(J, _GU[:, 0], _GU[:, 2])


def ucs_a_rgb(J, C, h_grados, informe=None, clave=""):
    h = np.deg2rad(h_grados)
    an, bn = neutro_ab(J)
    P = np.stack([J, an + C * np.cos(h), bn + C * np.sin(h)], -1)
    rgb = cspace_convert(P, "CAM02-UCS", "sRGB1")
    fuera = float(np.max(np.maximum(rgb - 1, 0) + np.maximum(-rgb, 0)))
    if informe is not None:
        informe[clave] = fuera
    return np.clip(rgb, 0, 1)


def J_de(v):
    """The single value -> lightness function shared by every ramp."""
    t = np.clip((np.asarray(v, float) - VMIN) / (VMAX - VMIN), 0, 1)
    return J_CLARO + (J_OSCURO - J_CLARO) * t


def rampa(m, n=256, informe=None):
    J = np.linspace(J_CLARO, J_OSCURO, n)
    return ListedColormap(ucs_a_rgb(J, croma(J), tono(MODELOS[m][2]), informe, f"gamut_rampa_{m}"), name=f"r_{m}")


def divergente(m, n=257, informe=None):
    """Delta map: neutral grey (statement lowers AUROC) <- neutral white -> model hue (statement raises AUROC).
    Equal |Delta| gives equal J' on both arms and in every model."""
    s = np.linspace(-1, 1, n)
    J = J_CENTRO + (J_OSCURO + 4 - J_CENTRO) * np.abs(s)
    Cm = croma(J) * np.clip(np.abs(s) / 0.08, 0, 1)          # neutral exactly at 0
    C = np.where(s >= 0, Cm, 0.0)   # negative arm: neutral grey, so it cannot be mistaken for any model hue
    H = np.where(s >= 0, tono(MODELOS[m][2]), H_CENIZA)
    return ListedColormap(ucs_a_rgb(J, C, H, informe, f"gamut_div_{m}"), name=f"d_{m}")


# ------------------------------------------------------------------------------------------------
# 2. Typography: TMLR text block (6.5 in), Latin Modern via LaTeX, sizes as in figuras_v2
# ------------------------------------------------------------------------------------------------
plt.rcParams.update(bundles.tmlr2023())
plt.rcParams.update({
    "text.latex.preamble": r"\usepackage[T1]{fontenc}\usepackage{lmodern}\usepackage{amsmath}\usepackage{amssymb}",
    "font.size": 8.5, "axes.labelsize": 8.5, "axes.titlesize": 8.5,
    "xtick.labelsize": 7.5, "ytick.labelsize": 7.5, "legend.fontsize": 7.5,
    "axes.linewidth": 0.5, "xtick.major.width": 0.5, "ytick.major.width": 0.5,
    "xtick.major.size": 2.5, "ytick.major.size": 2.5, "xtick.major.pad": 2, "ytick.major.pad": 2,
    "axes.edgecolor": CENIZA, "xtick.color": CENIZA, "ytick.color": CENIZA,
    "xtick.labelcolor": TEXTO, "ytick.labelcolor": TEXTO, "text.color": TEXTO, "axes.labelcolor": TEXTO,
    "pdf.fonttype": 42, "savefig.dpi": 300, "figure.constrained_layout.use": False,
})
ANCHO = 6.5


SALIDA = os.environ.get("ESCANER_SALIDA", AQUI)


def guardar(fig, nombre, **kw):
    for ext in ("pdf", "png"):
        fig.savefig(os.path.join(SALIDA, f"{nombre}.{ext}"), **kw)
    plt.close(fig)


def nombre_tex(m):
    n = MODELOS[m][0]
    return n if MODELOS[m][3] else r"\textit{" + n + "}"


# ------------------------------------------------------------------------------------------------
# 3. Data
# ------------------------------------------------------------------------------------------------
TRAMOS = (("pre", 0, 2), ("statement", 2, 42), ("between", 42, 44), ("Lean", 44, 84), ("question", 84, 92))
HUECO = 1.4   # blank gap (in column widths) drawn between spans, so the prompt's structure is visible


def disponibles():
    hay = {os.path.basename(f)[5:-4] for f in glob.glob(os.path.join(DATOS, "mapa_*.npz"))}
    desconocidos = hay - set(MODELOS)
    if desconocidos:
        print("warning: no palette entry for", sorted(desconocidos), "- skipped")
    return [m for m in ORDEN if m in hay]


def cargar(m):
    M = np.load(os.path.join(DATOS, f"mapa_{m}.npz"))
    c, s = M["completo"].astype(float), M["solo_lean"].astype(float)
    d = np.full_like(c, np.nan)
    d[:, 44:] = c[:, 44:] - s[:, 44:]          # what reading the statement adds, Lean + question columns only
    return c, s, d


def capa_fija(R):
    """Row of the layer fixed in advance for readout (ii), floor(2L/3), with L = R - 1 (row 0 = embeddings)."""
    return (2 * (R - 1)) // 3


def posiciones(tramos):
    """x offset of each span when spans are separated by HUECO; returns list of (name, a, b, x0) and total width."""
    out, x = [], 0.0
    for k, (nom, a, b) in enumerate(tramos):
        out.append((nom, a, b, x))
        x += (b - a) + (HUECO if k < len(tramos) - 1 else 0)
    return out, x


# ------------------------------------------------------------------------------------------------
# 4. Numeric checks
# ------------------------------------------------------------------------------------------------
def comprobaciones(modelos_todos):
    inf, gam = {}, {}
    vals = np.linspace(VMIN, VMAX, 41)
    Jtab, cvd = {}, {}
    for m in modelos_todos:
        cm = rampa(m, informe=gam)
        rgb = cm(np.linspace(0, 1, 256))[:, :3]
        J = cspace_convert(rgb, "sRGB1", "CAM02-UCS")[:, 0]
        Jtab[m] = cspace_convert(cm((vals - VMIN) / (VMAX - VMIN))[:, :3], "sRGB1", "CAM02-UCS")[:, 0]
        cvd[m] = {}
        for tipo in ("deuteranomaly", "protanomaly"):
            sim = np.clip(cspace_convert(rgb, {"name": "sRGB1+CVD", "cvd_type": tipo, "severity": 100}, "sRGB1"), 0, 1)
            Js = cspace_convert(sim, "sRGB1", "CAM02-UCS")[:, 0]
            cvd[m][tipo] = {"monotone": bool(np.all(np.diff(Js) < 0)), "J_light": round(float(Js[0]), 2), "J_dark": round(float(Js[-1]), 2)}
        dv = divergente(m, informe=gam)
        Jd = cspace_convert(dv(np.linspace(0, 1, 257))[:, :3], "sRGB1", "CAM02-UCS")[:, 0]
        inf.setdefault("divergente", {})[m] = {
            "neg_arm_increasing_to_centre": bool(np.all(np.diff(Jd[:129]) > 0)),
            "pos_arm_decreasing_from_centre": bool(np.all(np.diff(Jd[128:]) < 0)),
            "max_J_asymmetry_between_arms": round(float(np.max(np.abs(Jd[:129][::-1] - Jd[128:]))), 3)}
        inf.setdefault("secuencial", {})[m] = {
            "J_light": round(float(J[0]), 2), "J_dark": round(float(J[-1]), 2),
            "strictly_monotone": bool(np.all(np.diff(J) < 0)),
            "step_cv": round(float(np.std(np.diff(J)) / abs(np.mean(np.diff(J)))), 4)}
    A = np.array([Jtab[m] for m in modelos_todos])
    inf["max_J_spread_across_models_at_equal_AUROC"] = round(float(np.max(A.max(0) - A.min(0))), 3)
    Jdiv = np.array([cspace_convert(divergente(m)(np.linspace(0, 1, 257))[:, :3], "sRGB1", "CAM02-UCS")[:, 0] for m in modelos_todos])
    inf["max_J_spread_across_models_difference_map"] = round(float(np.max(Jdiv.max(0) - Jdiv.min(0))), 3)
    inf["cvd_severity_100"] = cvd
    inf["max_out_of_gamut_before_clip"] = round(max(gam.values()), 5)
    # identity colours: how far apart are the eight hues at the mid-ramp (AUROC 0.62), normal and simulated
    t = (0.62 - VMIN) / (VMAX - VMIN)
    mid = np.array([rampa(m)(t)[:3] for m in modelos_todos])
    dist = {}
    for tipo in ("normal", "deuteranomaly", "protanomaly"):
        X = mid if tipo == "normal" else np.clip(cspace_convert(mid, {"name": "sRGB1+CVD", "cvd_type": tipo, "severity": 100}, "sRGB1"), 0, 1)
        U = cspace_convert(X, "sRGB1", "CAM02-UCS")
        D = np.linalg.norm(U[:, None] - U[None], axis=-1)
        pares = {}
        for i in range(len(modelos_todos)):
            for j in range(i + 1, len(modelos_todos)):
                pares[f"{modelos_todos[i]}|{modelos_todos[j]}"] = round(float(D[i, j]), 2)
        mn = min(pares, key=pares.get)
        dist[tipo] = {"closest_pair": mn, "deltaE_closest": pares[mn],
                      "five_general_models_min": round(min(v for k, v in pares.items()
                                                           if all(x in ("olmo2_7b", "gemma3_4b", "llama31_8b", "qwen3_4b", "qwen3_8b") for x in k.split("|"))), 2)}
    inf["mid_ramp_deltaE_CAM02UCS_at_AUROC_0.62"] = dist
    return inf


# ------------------------------------------------------------------------------------------------
# 5. Swatch sheet
# ------------------------------------------------------------------------------------------------
def fig_paleta(presentes):
    filas = ORDEN
    fig = plt.figure(figsize=(ANCHO, 0.36 * len(filas) + 1.05))
    H = fig.get_figheight()
    y0 = 1 - 0.42 / H
    dy = 0.36 / H
    fig.text(0.02, 1 - 0.16 / H, r"Scan ramps: one Wada hue per model, one lightness scale for all", fontsize=9.5, va="center")
    xr0, xr1, xd0, xd1 = 0.625, 0.80, 0.84, 0.975
    for i, m in enumerate(filas):
        nom, wn, wh, pre = MODELOS[m]
        y = y0 - (i + 1) * dy
        fig.patches.append(plt.Rectangle((0.02, y + 0.12 * dy), 0.03, 0.62 * dy, transform=fig.transFigure, color=wh, lw=0))
        fig.text(0.062, y + 0.6 * dy, nombre_tex(m), fontsize=8.5, color=TEXTO, va="center")
        sufijo = "" if m in presentes else (r" \ (no data yet)" if m == "qwen3_8b" else r" \ (reserved)")
        fig.text(0.062, y + 0.18 * dy, rf"{wn} \ {wh.upper().replace('#', chr(92) + '#')} \ (Wada {COMBO[m]}){sufijo}", fontsize=7, color=CENIZA, va="center")
        axd = fig.add_axes([xd0, y + 0.18 * dy, xd1 - xd0, 0.55 * dy])
        axd.imshow(np.linspace(0, 1, 257)[None], aspect="auto", cmap=divergente(m), extent=(-DMAX, DMAX, 0, 1))
        axd.set_yticks([]); axd.set_xticks([])
        for sp in axd.spines.values():
            sp.set_visible(False)
        ax = fig.add_axes([xr0, y + 0.18 * dy, xr1 - xr0, 0.55 * dy])
        ax.imshow(np.linspace(0, 1, 256)[None], aspect="auto", cmap=rampa(m), extent=(VMIN, VMAX, 0, 1))
        ax.set_yticks([]); ax.set_xticks([])
        for s in ax.spines.values():
            s.set_visible(False)
    # grey row: the shared lightness, the same for every ramp
    y = y0 - (len(filas) + 1) * dy
    ax = fig.add_axes([xr0, y + 0.18 * dy, xr1 - xr0, 0.55 * dy])
    J = np.linspace(J_CLARO, J_OSCURO, 256)
    grey = ucs_a_rgb(J, 0 * J, 0.0)
    ax.imshow(grey[None], aspect="auto", extent=(VMIN, VMAX, 0, 1))
    ax.set_yticks([])
    ax.set_xticks([0.5, 0.6, 0.7]); ax.set_xticklabels(["0.5", "0.6", "0.7"])
    ax.tick_params(length=2, pad=1.5)
    for s in ax.spines.values():
        s.set_visible(False)
    ax.set_xlabel(r"out-of-fold AUROC", labelpad=2, fontsize=7.5)
    ax.tick_params(labelsize=7)
    axd = fig.add_axes([xd0, y + 0.18 * dy, xd1 - xd0, 0.55 * dy])
    Jd = J_CENTRO + (J_OSCURO + 4 - J_CENTRO) * np.abs(np.linspace(-1, 1, 257))
    axd.imshow(ucs_a_rgb(Jd, 0 * Jd, 0.0)[None], aspect="auto", extent=(-DMAX, DMAX, 0, 1))
    axd.set_yticks([]); axd.set_xticks([-0.12, 0, 0.12]); axd.set_xticklabels([r"$-0.12$", "0", r"$+0.12$"])
    axd.tick_params(length=2, pad=1.5, labelsize=7)
    for sp in axd.spines.values():
        sp.set_visible(False)
    axd.set_xlabel(r"$\Delta$ AUROC", labelpad=2, fontsize=7.5)
    fig.text(0.062, y + 0.45 * dy, r"lightness $J'$ shared by every ramp", fontsize=7, color=CENIZA, va="center")
    guardar(fig, "paleta_rampas")


# ------------------------------------------------------------------------------------------------
# 6. 2D scan for all models (v3: bilingual, grey arm below chance, noise floor of one cell, group headings)
# ------------------------------------------------------------------------------------------------
# AUROC map v3: the model ramp above chance (unchanged, J' 96 -> 24 for 0.50 -> 0.70) and a neutral grey arm below
# chance with the same lightness slope, so a cell at 0.45 is exactly as dark (in grey) as a cell at 0.55 (in hue).
# Nothing is clipped at 0.5 any more: the reader sees the below-chance cells, i.e. the size of the noise.
VMIN_BAJO = 0.38               # lowest cell over all maps is 0.391; nothing is clipped below
N_POS, N_NEG = 1, 1


def J_simetrica(v):
    return J_CLARO - (J_CLARO - J_OSCURO) * np.clip(np.abs(np.asarray(v, float) - 0.5) / (VMAX - VMIN), 0, 1)


def rampa_v3(m, n=321, informe=None):
    v = np.linspace(VMIN_BAJO, VMAX, n)
    J = J_simetrica(v)
    C = np.where(v >= 0.5, croma(J), 0.0)
    H = np.full_like(v, tono(MODELOS[m][2]))
    return ListedColormap(ucs_a_rgb(J, C, H, informe, f"gamut_rampa_v3_{m}"), name=f"r3_{m}")


# Noise floor of a single cell. Each cell is a Mann-Whitney AUROC of fixed scores (escaner_stats.py ranks the
# projections; the direction is not refitted per position). Under permuted labels its mean is 0.5 and, without ties,
# its variance is exactly (n0 + n1 + 1) / (12 n0 n1). We do not have the scores, only the maps, so we use the normal
# approximation to that permutation distribution: 5th-95th percentile = 0.5 -/+ 1.645 * sd.
N1, N0 = 250, 200
SD_CELDA = float(np.sqrt((N0 + N1 + 1) / (12 * N0 * N1)))          # 0.0274
Z95 = 1.6448536269514722
PISO = Z95 * SD_CELDA                                             # 0.0451
# Difference of two cells: if they were independent, sd * sqrt(2). Positive correlation (same items) makes it smaller,
# so this is an upper bound for non-negatively correlated cells, not an estimate.
PISO_DIF = Z95 * SD_CELDA * np.sqrt(2)                            # 0.0638

TXT = {
    "en": dict(
        tit=[r"statement + Lean", r"Lean alone", r"difference $\Delta$"],
        tramo={"statement": "statement", "Lean": "Lean", "question": "Q"},
        pre=r"\textbf{Level A replication models}", exp=r"\textbf{Other models}",
        clave_a=r"out-of-fold AUROC (grey: below chance)",
        clave_d=r"$\Delta$ = (statement + Lean) $-$ (Lean alone)",
        ruido=r"one cell, permuted labels, 5--95\%",
        ruido_d=r"same, if independent",
        nota=(r"Each key row is one model, in panel order: equal value, equal lightness in every hue. Grey: AUROC below 0.5, or $\Delta < 0$."
              "\n" r"Raw cells.  Q = question tokens (last column = last token).  $\blacktriangleright$ = layer $\lfloor 2L/3 \rfloor$, fixed for readout (ii)."
              "\n" r"Brackets: normal approximation to the permutation null of one cell, $n = 450$ (250/200): $0.5 \pm %.3f$." % PISO +
              "\n" r"About 5\% of cells pass it by chance in each direction.  All maps are exploratory, one seed."),
    ),
    "es": dict(
        tit=[r"enunciado + Lean", r"solo Lean", r"diferencia $\Delta$"],
        tramo={"statement": "enunciado", "Lean": "Lean", "question": "P"},
        pre=r"\textbf{Modelos de la réplica del Nivel A}", exp=r"\textbf{Otros modelos}",
        clave_a=r"AUROC fuera de pliegue (gris: bajo el azar)",
        clave_d=r"$\Delta$ = (enunciado + Lean) $-$ (solo Lean)",
        ruido=r"una celda, etiquetas permutadas, 5--95\%",
        ruido_d=r"igual, si fueran independientes",
        nota=(r"Cada fila de la clave es un modelo, en el orden de los paneles: igual valor, igual luminosidad en todos los tonos. Gris: AUROC"
              "\n" r"bajo 0.5, o $\Delta < 0$.  Celdas crudas.  P = tokens de la pregunta (última columna = último token).  $\blacktriangleright$ = capa $\lfloor 2L/3 \rfloor$, fija"
              "\n" r"para la lectura (ii).  Corchetes: aproximación normal a la nula por permutación de una celda, $n = 450$ (250/200): $0.5 \pm %.3f$." % PISO +
              "\n" r"Cerca del 5\% de las celdas la supera por azar en cada sentido.  Todos los mapas son exploratorios, una semilla."),
    ),
}


def dibujar_tramos(ax, Z, tramos, cmap, vmin, vmax):
    pos, W = posiciones(tramos)
    R = Z.shape[0]
    for nom, a, b, x0 in pos:
        # interpolation="none": the raw cells are embedded as an opaque image, one pixel per cell, with no resampling
        # and no soft mask (with "nearest", matplotlib adds a soft mask that poppler draws as a dark seam at the edge)
        # each cell is also replicated 8 x 8 (same value, nearest neighbour), so a viewer that smooths small embedded
        # images blurs only a sub-cell fringe, never across cells
        Zr = np.repeat(np.repeat(Z[:, a:b], 8, 0), 8, 1)
        ax.imshow(Zr, origin="lower", aspect="auto", cmap=cmap, vmin=vmin, vmax=vmax,
                  extent=(x0, x0 + (b - a), 0, R), interpolation="none")
    ax.set_xlim(0, W); ax.set_ylim(0, R)
    for s in ax.spines.values():
        s.set_visible(False)
    ax.set_xticks([]); ax.set_yticks([])
    return pos, W


def fig_2d(presentes, lang="en"):
    T = TXT[lang]
    n = len(presentes)
    TA = TRAMOS
    TB = TRAMOS[3:]
    _, WA = posiciones(TA)
    _, WB = posiciones(TB)
    sep = 7.0
    izq, der = 1.05, 0.22          # inches
    unidad = (ANCHO - izq - der) / (WA + 2 * WB + 2 * sep)
    alto_fila, hueco_fila = 0.62, 0.11
    cab = 0.20                     # height of a group heading line
    grupos = [m for k, m in enumerate(presentes) if k == 0 or MODELOS[m][3] != MODELOS[presentes[k - 1]][3]]
    paso = 0.052
    kh = paso * n
    nota_h = 0.112 * (T["nota"].count("\n") + 1) + 0.04
    ky = nota_h + 0.36            # bottom of the stacked key strips (inches)
    arriba, abajo = 0.30, ky + kh + 0.24 + 0.24
    H = arriba + n * alto_fila + (n - 1) * hueco_fila + len(grupos) * cab + abajo
    fig = plt.figure(figsize=(ANCHO, H))
    xs = [izq, izq + (WA + sep) * unidad, izq + (WA + WB + 2 * sep) * unidad]
    ws = [WA * unidad, WB * unidad, WB * unidad]
    recorte = {"auroc_below_%.2f" % VMIN_BAJO: 0, "auroc_above_%.2f" % VMAX: 0, "dif_hi": 0, "dif_lo": 0, "cells_dif": 0}
    cursor = H - arriba
    for i, m in enumerate(presentes):
        if m in grupos:
            cursor -= cab
            fig.text(0.02, (cursor + 0.04) / H, T["pre"] if MODELOS[m][3] else T["exp"], fontsize=8.5, va="bottom", ha="left")
        c, s, d = cargar(m)
        R = c.shape[0]
        y = cursor - alto_fila
        recorte["auroc_below_%.2f" % VMIN_BAJO] += int(np.sum(c < VMIN_BAJO) + np.sum(s[:, 44:] < VMIN_BAJO))
        recorte["auroc_above_%.2f" % VMAX] += int(np.sum(c > VMAX) + np.sum(s[:, 44:] > VMAX))
        recorte["dif_hi"] += int(np.sum(d[:, 44:] > DMAX)); recorte["dif_lo"] += int(np.sum(d[:, 44:] < -DMAX))
        recorte["cells_dif"] += int(d[:, 44:].size)
        cm, dv = rampa_v3(m), divergente(m)
        for k, (Z, tr, mapa, lo, hi) in enumerate(((c, TA, cm, VMIN_BAJO, VMAX), (s, TB, cm, VMIN_BAJO, VMAX), (d, TB, dv, -DMAX, DMAX))):
            ax = fig.add_axes([xs[k] / ANCHO, y / H, ws[k] / ANCHO, alto_fila / H])
            pos, W = dibujar_tramos(ax, Z, tr, mapa, lo, hi)
            if i == 0:
                ax.text(0, 1, T["tit"][k], transform=ax.transAxes, ha="left", va="bottom", fontsize=8.5)
                # column titles sit above the first group heading
                ax.texts[-1].set_y(1 + (cab + 0.06) / alto_fila)
            if i == n - 1:
                for nom, a, b, x0 in pos:
                    if nom in ("statement", "Lean", "question"):
                        ax.text(x0 + (b - a) / 2, -0.10 * R, T["tramo"][nom], ha="center", va="top", fontsize=7.5, color=TEXTO)
            if k == 0:
                ax.set_yticks([0.5, R - 0.5]); ax.set_yticklabels(["0", str(R - 1)])
                ax.tick_params(axis="y", length=2, pad=1.5, labelsize=7)
                f = capa_fija(R)
                ax.plot([-1.9], [f + 0.5], marker=">", ms=3.4, color=TEXTO, clip_on=False, mew=0)
        nom, wn, wh, pre = MODELOS[m]
        fig.text(0.02, (y + alto_fila * 0.62) / H, nombre_tex(m), color=wh, fontsize=8.5, va="center")
        fig.text(0.02, (y + alto_fila * 0.28) / H, rf"$L = {R - 1}$", color=CENIZA, fontsize=7, va="center")
        cursor = y - hueco_fila
    # keys: one strip per model, stacked, so the shared lightness is visible in the key itself

    def clave(x0, w, mapas, lo, hi, ticks, fmt, etiqueta, piso, txt_piso):
        top = ky + kh
        for j, mp in enumerate(mapas):
            a = fig.add_axes([x0 / ANCHO, (top - (j + 1) * paso + 0.007) / H, w / ANCHO, (paso - 0.007) / H])
            a.imshow(np.linspace(0, 1, 512)[None], aspect="auto", cmap=mp, extent=(lo, hi, 0, 1))
            a.set_xlim(lo, hi); a.set_yticks([])
            for sp in a.spines.values():
                sp.set_visible(False)
            if j < len(mapas) - 1:
                a.set_xticks([])
        a.set_xticks(ticks); a.set_xticklabels([fmt(t) for t in ticks]); a.tick_params(axis="x", length=2, pad=1.5, labelsize=7)
        a.set_xlabel(etiqueta, fontsize=7.5, labelpad=2)
        # noise bracket above the stacked strips, in data units of the key
        ab = fig.add_axes([x0 / ANCHO, (top + 0.015) / H, w / ANCHO, 0.20 / H])
        ab.set_xlim(lo, hi); ab.set_ylim(0, 1); ab.axis("off")
        c0 = 0.5 if lo > 0 else 0.0
        ab.plot([c0 - piso, c0 - piso, c0 + piso, c0 + piso], [0.03, 0.30, 0.30, 0.03], color=TEXTO, lw=0.6, solid_joinstyle="miter")
        ab.text(c0, 0.42, txt_piso, ha="center", va="bottom", fontsize=6.8, color=TEXTO)

    def fmt_a(t):
        return f"{t:.2f}"

    def fmt_d(t):
        return (r"$-$" if t < 0 else ("+" if t > 0 else "")) + f"{abs(t):.2f}"
    clave(xs[0] + 0.12 * ws[0], 0.78 * ws[0], [rampa_v3(m) for m in presentes], VMIN_BAJO, VMAX,
          [0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7], fmt_a, T["clave_a"], PISO, T["ruido"])
    clave(xs[2] - 0.55 * ws[1], ws[2] + 0.55 * ws[1], [divergente(m) for m in presentes], -DMAX, DMAX,
          [-0.12, -0.06, 0, 0.06, 0.12], fmt_d, T["clave_d"], PISO_DIF, T["ruido_d"])
    fig.text(0.02, 0.03 / H, T["nota"], fontsize=6.8, color=CENIZA, va="bottom", linespacing=1.3)
    sufijo = "" if lang == "en" else "_es"
    guardar(fig, "escaner2d_modelos" + sufijo)
    return recorte


# ------------------------------------------------------------------------------------------------
# 7. Relief: each layer is one slice (no interpolation across layers, none across models)
# ------------------------------------------------------------------------------------------------
SUAVE = 1.0   # light Gaussian smoothing along position inside a slice, in columns (relief only; 2D maps are raw)


def suavizar(z):
    if SUAVE <= 0:
        return z
    from scipy.ndimage import gaussian_filter1d
    return gaussian_filter1d(z, SUAVE, mode="nearest")


def relieve(ax, m, dx=0.95, dy=1.55, alto=24.0, fantasma=True, lw_borde=0.32, tramos=TRAMOS,
            etiquetas=True, fs=7.5, borde="white", cada_fantasma=1, lw_fantasma=0.28):
    """Oblique slice relief drawn in 2D with the painter's algorithm (deepest layer first, first layer in front).
    x = position (spans separated by gaps); each layer is one slice, shifted right by dx and up by dy per layer.
    Height above a slice's baseline = AUROC - 0.5 (cells below chance sit on the baseline), alto units per 0.1.
    Fill colour = the model ramp at that cell's AUROC (raw value). Slices are never joined to each other.
    Ash line on a slice = Lean alone at that layer (Lean and question spans)."""
    c, s, _ = cargar(m)
    R = c.shape[0]
    cm = rampa(m)
    tinta_fantasma = cm(0.9)
    pos, W = posiciones(tramos)
    zo = 1
    for l in range(R - 1, -1, -1):
        base, sx = l * dy, l * dx
        quads, cols = [], []
        lineas = []
        for nom, a, b, x0 in pos:
            zl = suavizar(c[l, a:b])      # colour and height both from the lightly smoothed slice
            h = (np.clip(zl, VMIN, None) - VMIN) / 0.1 * alto
            xc = x0 + np.arange(b - a) + 0.5 + sx
            he = np.concatenate([[h[0]], (h[:-1] + h[1:]) / 2, [h[-1]]])
            xe = np.concatenate([[xc[0] - 0.5], (xc[:-1] + xc[1:]) / 2, [xc[-1] + 0.5]])
            for j in range(b - a):
                quads.append([(xe[j], base), (xe[j], base + he[j]), (xc[j], base + h[j]),
                              (xe[j + 1], base + he[j + 1]), (xe[j + 1], base)])
                cols.append(cm(np.clip((zl[j] - VMIN) / (VMAX - VMIN), 0, 1)))
            xl = np.concatenate([[xe[0]], xc, [xe[-1]]])
            yl = base + np.concatenate([[he[0]], h, [he[-1]]])
            lineas.append(("borde", np.concatenate([[xe[0]], xl, [xe[-1]]]), np.concatenate([[base], yl, [base]])))
            if fantasma and a >= 44 and l % cada_fantasma == 0:
                hs = (np.clip(suavizar(s[l, a:b]), VMIN, None) - VMIN) / 0.1 * alto
                lineas.append(("fantasma", xc, base + hs))
        ax.add_collection(PolyCollection(quads, facecolors=cols, edgecolors=cols, linewidths=0.2, zorder=zo))
        for tipo, x, y in lineas:
            if tipo == "borde":
                ax.plot(x, y, color=borde, lw=lw_borde, zorder=zo + 0.6, solid_joinstyle="round")
            else:
                ax.plot(x, y, color=tinta_fantasma, lw=lw_fantasma, zorder=zo + 0.5, solid_joinstyle="round")
        zo += 1
    ytop = (R - 1) * dy + (VMAX - VMIN) / 0.1 * alto
    ax.set_xlim(-1, W + (R - 1) * dx + 1)
    ax.set_ylim(-4, ytop + 1)
    ax.set_aspect("equal")
    ax.axis("off")
    if etiquetas:
        for nom, a, b, x0 in pos:
            if nom in ("statement", "Lean", "question"):
                ax.text(x0 + (b - a) / 2, -1.5, nom if nom != "question" else "Q", ha="center", va="top",
                        fontsize=fs, style="italic", color=TEXTO)
    return R, W, dx, dy, alto


def escala_vertical(ax, x, alto, fs=7):
    """Small AUROC scale at the front-left corner: chance (0.5) and 0.6, in the relief's height units."""
    ax.plot([x, x], [0, alto], color=TEXTO, lw=0.45, solid_capstyle="butt")
    for v, yy in ((0.5, 0), (0.6, alto)):
        ax.plot([x - 0.9, x], [yy, yy], color=TEXTO, lw=0.45)
        ax.text(x - 1.6, yy, f"{v:.1f}", ha="right", va="center", fontsize=fs, color=TEXTO)


def flecha_capas(ax, W, R, dx, dy, fs=6.8):
    x0, y0 = W + 2.0, 0.0
    x1, y1 = W + 2.0 + (R - 1) * dx, (R - 1) * dy
    ax.annotate("", xy=(x1, y1), xytext=(x0, y0),
                arrowprops=dict(arrowstyle="-|>", lw=0.45, color=CENIZA, mutation_scale=5, shrinkA=0, shrinkB=0))
    ang = np.degrees(np.arctan2(dy, dx))
    ax.text((x0 + x1) / 2 + 1.6, (y0 + y1) / 2 - 1.0, r"layer", rotation=ang, rotation_mode="anchor",
            fontsize=fs, color=CENIZA, ha="center", va="top")
    ax.text(x0 - 0.3, y0 - 1.5, "0", fontsize=fs, color=CENIZA, ha="left", va="top")
    ax.text(x1 + 0.6, y1, f"{R - 1}", fontsize=fs, color=CENIZA, ha="left", va="center")


GEOM3D = dict(dx=0.45, dy=1.4, alto=14.0)


def fig_3d(presentes):
    n = len(presentes)
    nc = 2
    impar = n % 2 == 1
    nf = int(np.ceil(n / nc))
    W_cel, H_cel = ANCHO / nc, 2.3
    clave_h = 0.0 if impar else 0.62
    H = nf * H_cel + clave_h + 0.05
    fig = plt.figure(figsize=(ANCHO, H))
    for k, m in enumerate(presentes):
        f, col = divmod(k, nc)
        ax = fig.add_axes([(col * W_cel + 0.02) / ANCHO, (H - (f + 1) * H_cel) / H, (W_cel - 0.04) / ANCHO, (H_cel - 0.02) / H])
        R, W, dx, dy, alto = relieve(ax, m, **GEOM3D)
        ax.set_xlim(-11, W + (R - 1) * dx + 6)
        escala_vertical(ax, -2.2, alto)
        flecha_capas(ax, W, R, dx, dy)
        ytop = (R - 1) * dy + 2 * alto
        ax.text(-10.5, ytop, nombre_tex(m), color=MODELOS[m][2], fontsize=9, va="top", ha="left")
        ax.text(-10.5, ytop - 8.5, rf"$L = {R - 1}$", color=CENIZA, fontsize=7, va="top", ha="left")
    # key: either the free cell (odd n) or a strip under the panels (even n)
    if impar:
        x0, y0, w = (W_cel + 0.35) / ANCHO, (H - nf * H_cel + 0.95) / H, (W_cel - 0.7) / ANCHO
        ytxt = (H - nf * H_cel + 0.45) / H
        xtxt = (W_cel + 0.35) / ANCHO
    else:
        x0, y0, w = 0.37 / ANCHO, (clave_h - 0.30 + 0.04) / H, 2.3 / ANCHO
        ytxt = (clave_h - 0.18) / H
        xtxt = 3.35 / ANCHO
    hk = 0.045 * n
    axk = fig.add_axes([x0, y0, w, hk / H])
    for j, m in enumerate(presentes):
        axk.imshow(np.linspace(0, 1, 256)[None], aspect="auto", cmap=rampa(m), extent=(VMIN, VMAX, n - j - 1, n - j - 0.18))
    axk.set_ylim(0, n); axk.set_xlim(VMIN, VMAX); axk.set_yticks([])
    axk.set_xticks([0.5, 0.55, 0.6, 0.65, 0.7]); axk.set_xticklabels(["0.50", "0.55", "0.60", "0.65", "0.70"])
    axk.tick_params(axis="x", length=2, pad=1.5, labelsize=7)
    for sp in axk.spines.values():
        sp.set_visible(False)
    axk.set_xlabel(r"AUROC, statement + Lean (height and colour)", fontsize=7.5, labelpad=2)
    linea_y = ytxt + 0.1 / H
    fig.lines.append(plt.Line2D([xtxt, xtxt + 0.28 / ANCHO], [linea_y, linea_y], transform=fig.transFigure, color=TEXTO, lw=0.4))
    fig.text(xtxt + 0.34 / ANCHO, linea_y, r"Lean alone, same layer (dark line in each hue)", fontsize=7.5, va="center")
    fig.text(xtxt, ytxt - 0.07 / H, r"One slice per layer, first layer in front; slices are never joined." "\n"
             r"Height and colour lightly smoothed along position only" "\n" r"(Gaussian, $\sigma = 1$ column); the 2D scan shows raw cells.", fontsize=6.8, color=CENIZA, va="top", linespacing=1.25)
    guardar(fig, "escaner3d_modelos")


def fig_heroe(m="qwen3_4b"):
    if not os.path.exists(os.path.join(DATOS, f"mapa_{m}.npz")):
        return
    fig = plt.figure(figsize=(8.0, 5.0))
    ax = fig.add_axes([0.13, 0.02, 0.86, 0.83])
    R, W, dx, dy, alto = relieve(ax, m, dx=0.45, dy=1.6, alto=16.0, lw_borde=0.45, lw_fantasma=0.35, fs=10)
    ax.set_xlim(-2, W + (R - 1) * dx + 2)
    nom, wn, wh, pre = MODELOS[m]
    fig.text(0.05, 0.86, nom, color=wh, fontsize=20, va="center")
    fig.text(0.05, 0.79, r"layer $\times$ position", color=CENIZA, fontsize=10, va="center")
    fig.text(0.05, 0.735, r"One slice per layer, the first in front." "\n"
             r"Height and colour: AUROC of a linear probe," "\n" r"faithful vs.\ unfaithful formalization," "\n"
             r"reading the statement and the Lean." "\n"
             r"Dark line: the Lean alone.", color=CENIZA, fontsize=8, va="top", linespacing=1.4)
    guardar(fig, f"escaner3d_heroe_{m}", dpi=300)


if __name__ == "__main__":
    import sys
    presentes = disponibles()
    print("models found:", presentes)
    chk = comprobaciones(ORDEN)
    for lang in ("en", "es"):
        chk[f"clipping_in_2d_{lang}"] = fig_2d(presentes, lang)
    chk["noise_floor_one_cell"] = {"n1": N1, "n0": N0, "sd": round(SD_CELDA, 5), "p05_p95": [round(0.5 - PISO, 4), round(0.5 + PISO, 4)],
                                   "difference_if_independent": round(PISO_DIF, 4), "method": "normal approximation to the Mann-Whitney permutation null"}
    # v3 AUROC ramp: lightness symmetric about 0.5, grey arm below chance
    v = np.linspace(VMIN_BAJO, VMAX, 321)
    Jv = {m: cspace_convert(rampa_v3(m)(np.linspace(0, 1, 321))[:, :3], "sRGB1", "CAM02-UCS")[:, 0] for m in ORDEN}
    A = np.array(list(Jv.values()))
    chk["v3_ramp"] = {"max_J_spread_across_models": round(float(np.max(A.max(0) - A.min(0))), 3),
                      "J_at_0.45_vs_0.55_max_diff": round(float(max(abs(np.interp(0.45, v, J) - np.interp(0.55, v, J)) for J in Jv.values())), 3),
                      "monotone_each_arm": bool(all(np.all(np.diff(J[v <= 0.5]) > 0) and np.all(np.diff(J[v >= 0.5]) < 0) for J in Jv.values()))}
    if "todo" in sys.argv:
        fig_paleta(presentes); fig_3d(presentes); fig_heroe()
    chk["models_drawn"] = presentes
    with open(os.path.join(SALIDA, "comprobaciones_v3.json"), "w") as f:
        json.dump(chk, f, indent=1)
    print(json.dumps({k: v for k, v in chk.items() if k not in ("cvd_severity_100", "divergente", "secuencial")}, indent=1))
