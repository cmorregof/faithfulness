"""Recalcula SOLO el control «original frente a fiel» del análisis pareado (desviación del 6 nov 2026).
Reproduce la carga de datos y la condición completo/último de analizar_pares.py (mismas semillas,
particiones por archivo, capa por CV anidada) y aplica puntuar_originales con el emparejamiento por
archivo corregido. Escribe resultados/original_vs_fiel_<nombre>.json. No toca los JSON principales."""
import argparse, json, os, sys, time
import numpy as np
AQUI = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, AQUI)
import analizar_pares as AP
R = AP.R
ap = argparse.ArgumentParser(); ap.add_argument("--carpeta", required=True); ap.add_argument("--indice", required=True)
ap.add_argument("--nombre", required=True); ap.add_argument("--jobs", type=int, default=7); a = ap.parse_args()
t0 = time.time()
man = [json.loads(l) for l in open(os.path.join(a.carpeta, "manifiesto.jsonl"), encoding="utf-8")]
ind = {r["id"]: r for r in map(json.loads, open(a.indice, encoding="utf-8"))}
filas = [dict(ind[m["id"]], fila=j, grupo_man=m["grupo"]) for j, m in enumerate(man) if m["id"] in ind]
tren = [r for r in filas if r["rol"] in ("infiel", "fiel")]; orig = [r for r in filas if r["rol"] == "original"]
sel = np.array([r["fila"] for r in tren]); y = np.array([int(r["rol"] == "fiel") for r in tren])
g_origen = np.array([r["grupo_man"] for r in tren]); g = np.array([r.get("archivo") or r["grupo_man"] for r in tren])
pos_de = {(r["par"], r["rol"]): k for k, r in enumerate(tren)}; ids_par = sorted({r["par"] for r in tren})
pares = np.array([[pos_de[(p, "infiel")], pos_de[(p, "fiel")]] for p in ids_par]); gp = g_origen[pares[:, 0]]
Xc = R.acts(a.carpeta, "completo", "ultimo", sel)
res = R.correr_condicion(Xc, y, g, R.SEMILLAS, a.jobs); c, _ = R.puntajes(res, len(y))
auc = AP.auc_p(c, pares, gp)
sel_o = np.array([r["fila"] for r in orig]); g_o = np.array([r["grupo_man"] for r in orig])
a_o = np.array([r.get("archivo") or r["grupo_man"] for r in orig])
s_o = AP.puntuar_originales(res, Xc, y, g, R.acts(a.carpeta, "completo", "ultimo", sel_o), a_o)
cubiertos = int(np.sum(s_o != 0)); so = dict(zip(g_o, s_o))
w = np.array([1.0 if so[gg] > c[f] else (0.5 if so[gg] == c[f] else 0.0) for gg, f in zip(gp, pares[:, 1])])
out = dict(nombre=a.nombre, auroc_p_completo_reproducido=auc, originales=len(orig), originales_con_puntaje=cubiertos,
           p_original_mayor=float(AP.por_origen(w, gp).mean()),
           p_original_mayor_que_infiel=float(AP.por_origen(np.array([1.0 if so[gg] > c[i] else (0.5 if so[gg] == c[i] else 0.0) for gg, i in zip(gp, pares[:, 0])]), gp).mean()),
           nota="≈ 0,5 frente a la fiel si «haber sido editado» no es la señal; desviación del 6 nov (emparejamiento por archivo)",
           segundos=round(time.time() - t0, 1))
os.makedirs(os.path.join(AQUI, "resultados"), exist_ok=True)
json.dump(out, open(os.path.join(AQUI, "resultados", f"original_vs_fiel_{a.nombre}.json"), "w"), ensure_ascii=False, indent=1)
print(json.dumps(out, ensure_ascii=False))
