"""Prueba corta de punta a punta: tres capas, una semilla, 450 filas. No cambia probe.py.
Va por etapas porque esta terminal corta cada orden a los 180 s.
Uso: python paso1_reducida.py <etiqueta> <ultimo|media_lean|anidada_completo|anidada_solo_lean>"""
import hashlib, sys, time
from pathlib import Path
import numpy as np
R = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R))
import probe
AQUI = Path(__file__).resolve().parent
etiqueta, etapa = sys.argv[1], sys.argv[2]
CAPAS = [12, 24, 36]
print("sha256 probe.py:", hashlib.sha256((R / "probe.py").read_bytes()).hexdigest(), flush=True)
t0 = time.perf_counter()
guardar = {}
def datos(variante, posicion):
    X, y, g, man = probe.cargar(probe.CARPETA, variante, posicion)
    f = probe.subconjunto(man, True)
    return X[f][:, CAPAS, :], y[f], g[f], man, f
if etapa in ("ultimo", "media_lean"):
    Xc, y, g, man, f = datos("completo", etapa)
    Xl = datos("solo_lean", etapa)[0]
    probe._verificar_conteos(y, True)
    cc = probe.curva_por_capa(Xc, y, g, semillas=(0,), n_boot=200, verboso=False)
    cl = probe.curva_por_capa(Xl, y, g, semillas=(0,), n_boot=200, verboso=False)
    guardar["curva_comp"], guardar["curva_lean"] = cc["puntajes"], cl["puntajes"]
    print(etapa, "curva completo", np.round(cc["auroc"], 4), "solo_lean", np.round(cl["auroc"], 4), f"[{time.perf_counter()-t0:.0f} s]", flush=True)
    if etapa == "media_lean":
        pc, pl = cc["puntajes"][1], cl["puntajes"][1]
        print("  lectura (ii) reducida: completo", probe._fmt(*probe.ic_bootstrap(y, pc, g, n=500)), "solo_lean", probe._fmt(*probe.ic_bootstrap(y, pl, g, n=500)),
              "delta", probe._fmt(*probe.diferencia_pareada(y, pc, pl, g, n=500)), flush=True)
    else:
        bar = probe.control_barajadas(Xc, y, g, n_barajes=2, semilla=0)
        print("  barajadas", np.round(bar["auroc"], 3), flush=True)
        textos = probe._leer_lean(probe.PARQUET, man, True)
        sup = probe.linea_base_superficie([textos[i] for i in f], y, g, semillas=(0,))
        dice = probe.auroc_pyes(np.load(probe.CARPETA / "pyes_completo.npy")[f], y, g)
        print("  superficie", round(sup["auroc"], 4), "P(Yes) completo", round(dice["auroc"], 4), flush=True)
        guardar["superficie"] = sup["puntajes"]
        probe.figura_auroc_por_capa({"completo": cc, "solo_lean": cl, "barajadas": bar}, AQUI / f"reducida_{etiqueta}.png", titulo="prueba reducida", superficie=sup["auroc"])
else:
    variante = etapa.replace("anidada_", "")
    X, y, g, man, f = datos(variante, "ultimo")
    p, capas = probe.elegir_capa_anidada(X, y, g, semilla=0)
    print("anidada", variante, "capas (indice dentro de", CAPAS, ")", capas, "AUROC", round(probe.auroc(y, p), 4), flush=True)
    guardar["puntajes"], guardar["capas"] = p, np.array(capas)
np.savez(AQUI / f"reducida_{etiqueta}_{etapa}.npz", **guardar)
print(f"FIN {etapa} en {time.perf_counter()-t0:.0f} s", flush=True)
