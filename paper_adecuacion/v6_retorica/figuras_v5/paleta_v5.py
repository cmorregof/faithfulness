"""paleta_v5.py — paleta de los modelos para todas las figuras del artículo v5 y del README (17 nov 2026).

Encargo: observaciones del profesor Riaño sobre «Beyond the Lean Code Alone». La paleta Wada de v3 se leía lúgubre y
con demasiado morado (Qwen3-4B violeta, Llama-3.1 vino). Aquí hay tres candidatas; Carlos y el profesor Riaño escogen
una y se fija en ESCOGIDA. Solo cambia el color: el valor -> luminosidad de las rampas (J_de en escaner_v3.py) es el
mismo para todas las candidatas y todos los modelos.

Cada modelo lleva un color de identidad (líneas, nombres, puntos), dado como (tono h, luminosidad J', croma C) en
CAM02-UCS. Los tonos salen del concepto de cada candidata; J' y C se ajustaron (búsqueda al azar, ±6° de tono) para
separar los ocho colores con deuteranopía y protanopía simuladas (colorspacious, severidad 100) con contraste >= 3:1
sobre blanco. Las rampas del escáner y del relieve toman solo el tono h; su croma sigue una envolvente común a los modelos
(pico C_PICO en J_PICO), recortada para que la rampa de todos los modelos quepa en sRGB.
El gris ceniza de «Lean code alone» (#6E6878) no es parte de la paleta y no cambia.
"""
import numpy as np
from colorspacious import cspace_convert

NOMBRES = {   # nombre visible y si es modelo de la réplica prerregistrada (no cambia con la paleta)
    "olmo2_7b": ("OLMo-2-7B", True), "gemma3_4b": ("Gemma-3-4B", True), "llama31_8b": ("Llama-3.1-8B", True),
    "dsprover2_7b": ("DeepSeek-Prover-V2-7B", True), "qwen3_4b": ("Qwen3-4B", False),
    "goedel_8b": ("Goedel-Prover-V2-8B", False), "kimina_7b": ("Kimina-7B", False), "qwen3_8b": ("Qwen3-8B", False),
}
CINCO = ["qwen3_4b", "qwen3_8b", "olmo2_7b", "llama31_8b", "gemma3_4b"]
DEMOSTRADORES = ["dsprover2_7b", "goedel_8b", "kimina_7b"]

# Paleta v3 (Wada), para comparar y para la prueba de que nada más cambió.
WADA = dict(
    titulo="v3 (Wada), la actual",
    envolvente=dict(RECORTE=None, C_PICO=18.5, J_PICO=46.0, C_CLARO=2.5, C_OSCURO=13.0),
    hex={"olmo2_7b": "#437742", "gemma3_4b": "#A36752", "llama31_8b": "#7D133A", "dsprover2_7b": "#004F46",
         "qwen3_4b": "#4F4086", "goedel_8b": "#A36AA5", "kimina_7b": "#635A3A", "qwen3_8b": "#064F6E"},
)

CANDIDATAS = {
    # A: fría y equilibrada. Qwen en azul y turquesa, OLMo verde, Gemma ámbar, Llama coral. Un solo tono morado:
    #    la orquídea de Goedel.
    "A": dict(
        titulo="A · Mar y arena",
        envolvente=dict(RECORTE=0.94, C_PICO=30.0, J_PICO=50.0, C_CLARO=4.0, C_OSCURO=15.0),
        hJC={"qwen3_4b": (249, 54, 25), "qwen3_8b": (193, 52, 15), "olmo2_7b": (146, 44, 20),
             "gemma3_4b": (74, 62, 21), "llama31_8b": (32, 44, 33),
             "dsprover2_7b": (108, 50, 18), "goedel_8b": (324, 45, 32), "kimina_7b": (51, 52, 27)},
    ),
    # B: pastel (inspirada en la escala «light» de Paul Tol, pensada para daltonismo). Rampas con el croma alto en
    #    la zona clara; líneas un punto más claras que en A. El único tono cercano al morado es el rosa
    #    malva de Goedel.
    "B": dict(
        titulo="B · Pastel (Tol claro)",
        envolvente=dict(RECORTE=0.94, C_PICO=28.0, J_PICO=64.0, C_CLARO=6.0, C_OSCURO=12.0),
        hJC={"qwen3_4b": (240, 62, 24), "qwen3_8b": (166, 56, 19), "olmo2_7b": (111, 62, 27),
             "gemma3_4b": (38, 50, 34), "llama31_8b": (7, 66, 29),
             "dsprover2_7b": (219, 51, 21), "goedel_8b": (349, 56, 28), "kimina_7b": (92, 52, 18)},
    ),
    # C: cálida. La familia Qwen en terracota y azafrán, Gemma turquesa, Llama azul de mar, OLMo salvia.
    #    Un solo tono morado: el ciruela de Goedel.
    "C": dict(
        titulo="C · Mediterráneo",
        envolvente=dict(RECORTE=0.94, C_PICO=30.0, J_PICO=52.0, C_CLARO=4.0, C_OSCURO=15.0),
        hJC={"qwen3_4b": (32, 42, 35), "qwen3_8b": (73, 59, 25), "olmo2_7b": (142, 47, 22),
             "gemma3_4b": (195, 60, 17), "llama31_8b": (242, 52, 22),
             "dsprover2_7b": (106, 58, 20), "goedel_8b": (316, 55, 33), "kimina_7b": (51, 50, 26)},
    ),
}

ESCOGIDA = "A"   # escogida por Carlos el 17 nov 2026 (opacidad del relieve: 0.60, en escaner3d_v5.py)


def croma_maxima(J, h, a0=0.0, b0=0.0):
    """Mayor croma C' de CAM02-UCS que cabe en sRGB con luminosidad J' y tono h, medida desde el centro (a0, b0)
    (escaner_v3 usa el gris neutro de sRGB de cada J'). Bisección, vectorizada en J."""
    J = np.atleast_1d(np.asarray(J, float))
    lo, hi = np.zeros_like(J), np.full_like(J, 80.0)
    ca, sa = np.cos(np.deg2rad(h)), np.sin(np.deg2rad(h))
    for _ in range(30):
        C = (lo + hi) / 2
        rgb = cspace_convert(np.stack([J, a0 + C * ca, b0 + C * sa], -1), "CAM02-UCS", "sRGB1")
        ok = np.all((rgb >= 0) & (rgb <= 1), -1)
        lo, hi = np.where(ok, C, lo), np.where(ok, hi, C)
    return lo


def ucs_a_hex(J, C, h):
    """Color de CAM02-UCS (J', C', h) a hex sRGB. Falla si queda fuera de la gama, para no recortar en silencio."""
    a, b = C * np.cos(np.deg2rad(h)), C * np.sin(np.deg2rad(h))
    rgb = cspace_convert(np.array([J, a, b], float), "CAM02-UCS", "sRGB1")
    assert np.all(rgb > -1e-3) and np.all(rgb < 1 + 1e-3), ("fuera de gama", J, C, h, rgb)
    rgb = np.clip(rgb, 0, 1)
    return "#" + "".join(f"{int(round(v * 255)):02X}" for v in rgb)


def hexes(nombre):
    p = WADA if nombre == "WADA" else CANDIDATAS[nombre]
    if "hex" in p:
        return dict(p["hex"])
    return {m: ucs_a_hex(J, C, h) for m, (h, J, C) in p["hJC"].items()}


def modelos(nombre):
    """El diccionario MODELOS con la forma que espera escaner_v3: (nombre, etiqueta del color, hex, ¿prerregistrado?)."""
    hx = hexes(nombre)
    return {m: (n, f"{nombre}:{m}", hx[m], pre) for m, (n, pre) in NOMBRES.items()}


def envolvente(nombre):
    return dict((WADA if nombre == "WADA" else CANDIDATAS[nombre])["envolvente"])


def aplicar(E, nombre):
    """Instala la paleta `nombre` en el módulo escaner_v3 ya importado (colores de identidad y envolvente de croma)."""
    E.MODELOS.clear()
    E.MODELOS.update(modelos(nombre))
    for k, v in envolvente(nombre).items():
        setattr(E, k, v)
