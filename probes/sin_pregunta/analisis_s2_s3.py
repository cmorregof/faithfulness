"""Análisis S2 y S3 de probes/sin_pregunta/regla_BORRADOR.md (regla aprobada por Carlos el 11 nov 2026).

Todo es exploratorio y post hoc. No cambia ninguna decisión del piloto.

  --paso s2a   El último token SIN la pregunta, Nivel A (450 filas que compilan).
               Mismo procedimiento que la lectura (i) del prerregistro v2: se llama a
               referencia/prerregistro_v2_analisis.py (condicion, particiones_fijas) sin modificarlo.
               Δ_sp = AUROC(full sin pregunta) − AUROC(lean_only sin pregunta), y Δ − Δ_sp contra los
               puntajes fuera de partición ya guardados (referencia/v2_puntajes_<nombre>_i_ultimo_cv.npz).
  --paso s2b   Lo mismo en el Nivel B (377 pares): AUROC pareada, capa por validación cruzada anidada,
               bootstrap de orígenes; el Δ original se recalcula con el mismo código y debe reproducir
               el del artículo.
  --paso s3    Controles del Nivel B frente a la segunda lectura (media sobre los tokens de Lean):
               n-gramas de ambos textos, superficie cruzada, P(Yes) y un control combinado (n-gramas +
               rasgos cruzados en un clasificador); también sin C2 y por familia (A, B, C2, C3).
  --paso resumen   Tabla de S3 con los modelos ya analizados y la frase que la regla permite.

No modifica nada: importa nivel_b/analizar_pares.py y referencia/probe_referencia.py. Sin la marca
probes/intervencion/APROBADO_regla (con el SHA-256 de la regla tal como está hoy) solo corre --prueba.

Uso (desde la raíz de Proyecto Godel; PY=biblioteca/.venv/bin/python):
  $PY -I probes/sin_pregunta/analisis_s2_s3.py --paso s3 --nombre qwen3_4b     # y olmo2_7b, llama31_8b, gemma3_4b
  $PY -I probes/sin_pregunta/analisis_s2_s3.py --paso resumen
  $PY -I probes/sin_pregunta/analisis_s2_s3.py --paso s2a --nombre qwen3_4b
  $PY -I probes/sin_pregunta/analisis_s2_s3.py --paso s2b --nombre qwen3_4b
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse
import hashlib
import importlib.util
import json
import re
import sys
import time

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
PROBES = os.path.dirname(AQUI)
for _p in (os.path.join(PROBES, "nivel_b"), os.path.join(PROBES, "referencia")):
    sys.path.insert(0, _p)
MARCA = os.path.join(PROBES, "intervencion", "APROBADO_regla")
REGLA = os.path.join(AQUI, "regla_BORRADOR.md")
MODELOS_B = ("qwen3_4b", "olmo2_7b", "llama31_8b", "gemma3_4b")
N_BOOT = 2000


def exigir_marca(prueba):
    if prueba:
        print("PRUEBA: una semilla y una de cada seis capas. Lo que salga NO es un resultado.\n")
        return
    if not os.path.exists(MARCA):
        sys.exit("Falta probes/intervencion/APROBADO_regla (la crea Carlos). Sin ella solo corre --prueba.")
    sha = hashlib.sha256(open(REGLA, "rb").read()).hexdigest()
    if sha not in open(MARCA, encoding="utf-8").read():
        sys.exit("La regla cambió después de aprobarse (su SHA-256 no está en la marca). No corro.")


def ic(v):
    return [float(x) for x in np.percentile(v, [2.5, 97.5])]


def guardar(a, nombre, out):
    d = os.path.join(AQUI, "resultados" + ("_prueba" if a.prueba else ""))
    os.makedirs(d, exist_ok=True)
    ruta = os.path.join(d, nombre + ".json")
    json.dump(out, open(ruta, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(f"\nguardado en {os.path.relpath(ruta, PROBES)}")


# ---------------------------------------------------------------- Nivel B: datos y puntajes

def datos_b(carpeta):
    """Como analizar_pares.main: filas de los pares, particiones por archivo, pares y orígenes."""
    import pyarrow.parquet as pq
    indice = os.path.join(PROBES, "nivel_b", "datos", "pares_indice_principal.jsonl")
    man = [json.loads(l) for l in open(os.path.join(carpeta, "manifiesto.jsonl"), encoding="utf-8")]
    ind = {r["id"]: r for r in map(json.loads, open(indice, encoding="utf-8"))}
    filas = [dict(ind[m["id"]], fila=j, grupo_man=m["grupo"]) for j, m in enumerate(man) if m["id"] in ind]
    tren = [r for r in filas if r["rol"] in ("infiel", "fiel")]
    d = {"sel": np.array([r["fila"] for r in tren]), "y": np.array([int(r["rol"] == "fiel") for r in tren]),
         "g": np.array([r.get("archivo") or r["grupo_man"] for r in tren]),
         "ids": [m["id"] for m in man]}
    g_origen = np.array([r["grupo_man"] for r in tren])
    pos_de = {(r["par"], r["rol"]): k for k, r in enumerate(tren)}
    ids_par = sorted({r["par"] for r in tren})
    d["pares"] = np.array([[pos_de[(p, "infiel")], pos_de[(p, "fiel")]] for p in ids_par])
    d["info_par"] = [tren[pos_de[(p, "infiel")]] for p in ids_par]
    d["gp"] = g_origen[d["pares"][:, 0]]
    filas_pq = pq.read_table(os.path.join(PROBES, "nivel_b", "datos", "pares_nivel_b.parquet")).to_pylist()
    d["lean"] = [filas_pq[r["id"]]["autoformalization"] for r in tren]
    d["nl"] = [filas_pq[r["id"]]["refined_statement"] for r in tren]
    return d


def puntajes_b(a, carpeta, variante, posicion, d, semillas):
    """Puntajes fuera de partición con capa por validación cruzada anidada (probe_referencia)."""
    import probe_referencia as R
    X = R.acts(carpeta, variante, posicion, d["sel"])
    if a.prueba:
        X = X[:, ::6]
    res = R.correr_condicion(X, d["y"], d["g"], semillas, a.jobs)
    return R.puntajes(res, len(d["y"]))[0]


def tarea_combinada(lean, nl, F, y, tr, te):
    """Como probe_referencia.tarea_superficie con el NL (n-gramas y longitudes de los dos textos), más
    los rasgos de superficie cruzada estandarizados, en una sola regresión logística."""
    import probe_referencia as R
    from scipy import sparse
    from sklearn.feature_extraction.text import CountVectorizer
    from sklearn.preprocessing import StandardScaler
    btr, bte = [], []
    for textos in (lean, nl):
        v = CountVectorizer(binary=True, ngram_range=(1, 2), min_df=2, token_pattern=R.TOKEN_LEAN, lowercase=False)
        v.fit([textos[i] for i in tr])
        btr.append(v.transform([textos[i] for i in tr]))
        bte.append(v.transform([textos[i] for i in te]))
        largo = np.array([[np.log1p(len(t)), np.log1p(len(re.findall(R.TOKEN_LEAN, t)))] for t in textos])
        esc = StandardScaler().fit(largo[tr])
        btr.append(sparse.csr_matrix(esc.transform(largo[tr])))
        bte.append(sparse.csr_matrix(esc.transform(largo[te])))
    esc = StandardScaler().fit(F[tr])
    btr.append(sparse.csr_matrix(esc.transform(F[tr])))
    bte.append(sparse.csr_matrix(esc.transform(F[te])))
    m = R.lr().fit(sparse.hstack(btr).tocsr(), y[tr])
    return m.predict_proba(sparse.hstack(bte).tocsr())[:, 1]


def combinada(lean, nl, F, y, g, semillas):
    import probe_referencia as R
    todas = []
    for s in semillas:
        v = np.full(len(y), np.nan)
        for tr, te in R.particiones(y, g, s):
            v[te] = tarea_combinada(lean, nl, F, y, tr, te)
        todas.append(v)
    return np.mean(todas, 0)


# ---------------------------------------------------------------- S3

def paso_s3(a):
    import analizar_pares as AP
    import probe_referencia as R
    exigir_marca(a.prueba)
    t0 = time.time()
    carpeta = os.path.join(PROBES, "activaciones", "nivel_b_" + a.nombre)
    d = datos_b(carpeta)
    y, g, pares, gp, info = d["y"], d["g"], d["pares"], d["gp"], d["info_par"]
    semillas = (0,) if a.prueba else R.SEMILLAS
    print(f"{len(pares)} pares en {len(np.unique(gp))} orígenes; modelo {a.nombre}", flush=True)

    S = {}
    S["full_media"] = puntajes_b(a, carpeta, "completo", "media_lean", d, semillas)
    print(f"  full, media sobre Lean: {AP.auc_p(S['full_media'], pares, gp):.3f} ({time.time() - t0:.0f} s)", flush=True)
    S["full_ultimo"] = puntajes_b(a, carpeta, "completo", "ultimo", d, semillas)
    print(f"  full, último token:     {AP.auc_p(S['full_ultimo'], pares, gp):.3f} ({time.time() - t0:.0f} s)", flush=True)
    S["ngramas"] = R.superficie(d["lean"], d["nl"], y, g, semillas, True, a.jobs)[0]
    F = np.array([AP.rasgos_cruzados(n, le) for n, le in zip(d["nl"], d["lean"])], dtype=float)
    S["cruzada"] = AP.cruzada(F, y, g, semillas)
    S["combinada"] = combinada(d["lean"], d["nl"], F, y, g, semillas)
    py = np.load(os.path.join(carpeta, "pyes_completo.npy"))[d["sel"]]
    S["p_yes"] = py[:, 4] / np.maximum(py[:, 4] + py[:, 5], 1e-12)
    controles = ("ngramas", "cruzada", "p_yes", "combinada")

    def bloque(m):
        p, o = pares[m], gp[m]
        if len(p) < 10:
            return {"n_pares": int(len(p)), "nota": "menos de 10 pares; no se reporta"}
        b = {"n_pares": int(len(p)), "auroc": {k: list(AP.boot_p([S[k]], p, o)[0]) for k in S}}
        for lectura in ("full_media", "full_ultimo"):
            b[lectura + "_menos"] = {c: list(AP.boot_p([S[lectura], S[c]], p, o)[2]) for c in controles}
        return b

    todo = np.ones(len(pares), bool)
    c2 = np.array([i["regla"].startswith("C2") for i in info])
    c3 = np.array([i["regla"].startswith("C3") for i in info])
    out = {"modelo": a.nombre, "n_pares": int(len(pares)), "n_origenes": int(len(np.unique(gp))),
           "semillas": list(semillas), "principal": bloque(todo), "sin_C2": bloque(~c2),
           "familia_A": bloque(np.array([i["familia"] == "A" for i in info])),
           "familia_B": bloque(np.array([i["familia"] == "B" for i in info])),
           "C2": bloque(c2), "C3": bloque(c3)}
    dif = out["principal"]["full_media_menos"]
    out["supera_en_la_segunda_lectura"] = {c: bool(dif[c][1] > 0) for c in ("ngramas", "cruzada", "p_yes")}
    out["supera_los_tres"] = all(out["supera_en_la_segunda_lectura"].values())
    out["segundos"] = round(time.time() - t0, 1)
    f = lambda t: f"{t[0]:+.3f} [{t[1]:+.3f}, {t[2]:+.3f}]"
    print("\nAUROC pareada:", {k: round(v[0], 3) for k, v in out["principal"]["auroc"].items()})
    for lectura in ("full_media", "full_ultimo"):
        print(f"{lectura} menos:", {c: f(v) for c, v in out["principal"][lectura + "_menos"].items()})
    print("sin C2, full_media menos:", {c: f(v) for c, v in out["sin_C2"]["full_media_menos"].items()})
    print("supera los tres controles en la segunda lectura:", out["supera_los_tres"])
    guardar(a, f"s3_{a.nombre}", out)
    return out


def paso_resumen(a):
    d = os.path.join(AQUI, "resultados")
    hechos = [m for m in MODELOS_B if os.path.exists(os.path.join(d, f"s3_{m}.json"))]
    if not hechos:
        sys.exit("No hay resultados de S3 todavía.")
    f = lambda t: f"{t[0]:+.3f} [{t[1]:+.3f}, {t[2]:+.3f}]"
    k = 0
    print("| modelo | full (media) | − n-gramas | − cruzada | − P(Yes) | − combinada | sin C2: − n-gramas |")
    print("|---|---|---|---|---|---|---|")
    for m in hechos:
        r = json.load(open(os.path.join(d, f"s3_{m}.json"), encoding="utf-8"))
        p = r["principal"]["full_media_menos"]
        k += r["supera_los_tres"]
        print(f"| {m} | {r['principal']['auroc']['full_media'][0]:.3f} | {f(p['ngramas'])} | {f(p['cruzada'])} | "
              f"{f(p['p_yes'])} | {f(p['combinada'])} | {f(r['sin_C2']['full_media_menos']['ngramas'])} |")
    print(f"\nEn la segunda lectura, {k} de los {len(hechos)} modelos analizados superan los dos controles de "
          "superficie y su propio P(Yes) con intervalos por encima de cero.")
    if len(hechos) < len(MODELOS_B):
        print("Faltan:", ", ".join(m for m in MODELOS_B if m not in hechos))


# ---------------------------------------------------------------- S2, Nivel B

def paso_s2b(a):
    import analizar_pares as AP
    import probe_referencia as R
    exigir_marca(a.prueba)
    t0 = time.time()
    ref = os.path.join(PROBES, "activaciones", "nivel_b_" + a.nombre)
    sp = os.path.join(PROBES, "activaciones", "sin_pregunta", "nivel_b_" + a.nombre)
    d = datos_b(ref)
    if d["ids"] != [json.loads(l)["id"] for l in open(os.path.join(sp, "manifiesto.jsonl"), encoding="utf-8")]:
        sys.exit("Las filas sin pregunta no son las de la extracción original. No comparo.")
    pares, gp = d["pares"], d["gp"]
    semillas = (0,) if a.prueba else R.SEMILLAS
    S = {}
    for nombre, carpeta in (("con", ref), ("sin", sp)):
        for v in ("completo", "solo_lean"):
            S[nombre, v] = puntajes_b(a, carpeta, v, "ultimo", d, semillas)
            print(f"  {v}, {nombre} pregunta: {AP.auc_p(S[nombre, v], pares, gp):.3f} ({time.time() - t0:.0f} s)", flush=True)
    con = AP.boot_p([S["con", "completo"], S["con", "solo_lean"]], pares, gp)
    sin = AP.boot_p([S["sin", "completo"], S["sin", "solo_lean"]], pares, gp)
    W = np.array([AP.por_origen(AP.w_pares(S[k], pares), gp)
                  for k in (("con", "completo"), ("con", "solo_lean"), ("sin", "completo"), ("sin", "solo_lean"))])
    rng = np.random.default_rng(0)
    m = W.shape[1]
    reps = np.array([W[:, rng.integers(0, m, m)].mean(1) for _ in range(N_BOOT)])
    dd = (reps[:, 0] - reps[:, 1]) - (reps[:, 2] - reps[:, 3])
    out = {"modelo": a.nombre, "nivel": "B", "n_pares": int(len(pares)), "n_origenes": int(m), "semillas": list(semillas),
           "con_pregunta": {"full": list(con[0]), "lean_only": list(con[1]), "delta": list(con[2])},
           "sin_pregunta": {"full": list(sin[0]), "lean_only": list(sin[1]), "delta_sp": list(sin[2])},
           "delta_menos_delta_sp": [float(con[2][0] - sin[2][0]), *ic(dd)],
           "segundos": round(time.time() - t0, 1)}
    out["lectura"] = ("en el último token la brecha no requiere la pregunta" if sin[2][1] > 0 else
                      "sin la pregunta la brecha no se establece en el último token")
    print(json.dumps(out, ensure_ascii=False, indent=1))
    guardar(a, f"s2b_{a.nombre}", out)
    return out


# ---------------------------------------------------------------- S2, Nivel A

def paso_s2a(a):
    exigir_marca(a.prueba)
    t0 = time.time()
    spec = importlib.util.spec_from_file_location("prerregistro_v2_analisis",
                                                  os.path.join(PROBES, "referencia", "prerregistro_v2_analisis.py"))
    V = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(V)
    import torch
    torch.set_num_threads(a.jobs)
    sp = os.path.join(PROBES, "activaciones", "sin_pregunta", a.nombre)
    man = [json.loads(l) for l in open(os.path.join(sp, "manifiesto.jsonl"), encoding="utf-8")]
    filas = np.flatnonzero(np.array([m["compila"] for m in man]) == 1)       # posición en las activaciones
    y = np.array([m["etiqueta"] for m in man])[filas]
    g = np.array([m["grupo"] for m in man])[filas]
    semillas = (0,) if a.prueba else V.SEMILLAS
    parts = V.particiones_fijas(y, g, semillas)
    P = {}
    for v in ("completo", "solo_lean"):
        X = V.ref.acts(sp, v, "ultimo", filas)
        if a.prueba:
            X = X[:, ::6]
        P[v] = V.condicion(X, y[:, None].astype(np.int8), parts, capa_fija=None)[0][:, 0]
        print(f"  {v} sin pregunta: AUROC {V.ref.auc(y, P[v]):.3f} ({time.time() - t0:.0f} s)", flush=True)
    b = V.ref.bootstrap(y, g, [P["completo"], P["solo_lean"]])
    out = {"modelo": a.nombre, "nivel": "A", "n": int(len(y)), "semillas": list(semillas),
           "sin_pregunta": {"full": list(b[0]), "lean_only": list(b[1]), "delta_sp": list(b[2])}}
    ruta = os.path.join(PROBES, "referencia", f"v2_puntajes_{a.nombre}_i_ultimo_cv.npz")
    if os.path.exists(ruta):
        z = np.load(ruta)
        if len(z["y"]) == len(y) and (z["y"] == y).all():
            c, l = z["completo"], z["solo_lean"]
            bo = V.ref.bootstrap(y, g, [c, l])
            # Δ − Δ_sp con los mismos remuestreos de grupos, estratificados por clase (como ref.bootstrap)
            rng = np.random.default_rng(0)
            ug, primera = np.unique(g, return_index=True)
            clase = y[primera]
            de = {k: np.flatnonzero(g == k) for k in ug}
            pos, neg = ug[clase == 1], ug[clase == 0]
            dd = []
            for _ in range(N_BOOT):
                el = np.concatenate([rng.choice(pos, len(pos)), rng.choice(neg, len(neg))])
                i = np.concatenate([de[k] for k in el])
                if len(np.unique(y[i])) < 2:
                    continue
                A = V.ref.auc
                dd.append((A(y[i], c[i]) - A(y[i], l[i])) - (A(y[i], P["completo"][i]) - A(y[i], P["solo_lean"][i])))
            out["con_pregunta"] = {"full": list(bo[0]), "lean_only": list(bo[1]), "delta": list(bo[2]),
                                   "fuente": os.path.relpath(ruta, PROBES)}
            out["delta_menos_delta_sp"] = [float(bo[2][0] - b[2][0]), *ic(dd)]
        else:
            out["con_pregunta"] = "los puntajes guardados no corresponden a estas filas; no se compara"
    else:
        out["con_pregunta"] = "no hay puntajes guardados de la lectura (i) para este modelo"
    out["lectura"] = ("en el último token la brecha no requiere la pregunta" if b[2][1] > 0 else
                      "sin la pregunta la brecha no se establece en el último token")
    out["segundos"] = round(time.time() - t0, 1)
    print(json.dumps(out, ensure_ascii=False, indent=1))
    guardar(a, f"s2a_{a.nombre}", out)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paso", required=True, choices=["s2a", "s2b", "s3", "resumen"])
    ap.add_argument("--nombre", default="qwen3_4b")
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--prueba", action="store_true", help="una semilla y una de cada seis capas; no exige la marca")
    a = ap.parse_args()
    {"s2a": paso_s2a, "s2b": paso_s2b, "s3": paso_s3, "resumen": paso_resumen}[a.paso](a)


if __name__ == "__main__":
    main()
