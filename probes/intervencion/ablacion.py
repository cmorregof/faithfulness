"""Ablación de la dirección de la sonda sobre los pares certificados del Nivel B (11 nov 2026).

PREGUNTA. La sonda de la lectura (ii) separa las formalizaciones adecuadas de las inadecuadas leyendo
la media sobre los tokens de Lean, antes de que el modelo vea la pregunta. ¿Usa el modelo esa
dirección cuando responde? Aquí se le quita mientras lee el Lean y se mira si su propio P(Yes)
deja de distinguir, dentro de cada par, el miembro adecuado del inadecuado.

QUÉ SE HACE, en tres pasos:

  direcciones (CPU, segundos)
      Con las activaciones ya guardadas («completo», media sobre Lean, capa fija ⌊2L/3⌋) ajusta la
      sonda fuera de partición: cinco particiones agrupadas por archivo fuente (semilla 0), y cada
      fila recibe la dirección ajustada SIN ella. Guarda también la dirección de la sonda de
      «solo_lean» (control de especificidad) y K direcciones al azar (control de tamaño).
  correr (GPU)
      Para cada fila de los pares corre el prompt normal, con la pregunta, y lee P(« Yes») y
      P(« No») tras «**Answer:», como el P(Yes) del artículo. Lo hace sin intervenir («base») y con
      cada dirección ablacionada. Ablación por la media: en los tokens de Lean, en los embeddings y en
      la salida de cada bloque menos el último, la coordenada del residual a lo largo de la dirección
      se fija en su media de entrenamiento,
          h  <-  h - ((h·d) - m_capa) d.
      Así se borra lo que esa dirección distingue entre filas sin sacar al modelo de su rango.
  analizar (CPU, segundos)
      AUROC pareada de P(Yes) en cada condición; caída = base - condición. Compara la caída de la
      sonda con las K caídas al azar y con la de «solo_lean», con bootstrap de orígenes.

NO modifica nada existente: importa probes/extraer.py (prompt, ids de Yes/No), probes/nivel_b/
analizar_pares.py (AUROC pareada, bootstrap) y probes/referencia/probe_referencia.py (particiones,
regresión). «correr» completo y «analizar» exigen probes/intervencion/APROBADO_regla, que crea
Carlos al aprobar la sección S4 de probes/sin_pregunta/regla_BORRADOR.md.

Uso (desde la raíz de Proyecto Godel; PY=biblioteca/.venv/bin/python):
  $PY -I probes/intervencion/ablacion.py --paso direcciones
  HF_HUB_OFFLINE=1 $PY -I probes/intervencion/ablacion.py --paso correr --prueba 4    # humo: 4 pares
  HF_HUB_OFFLINE=1 caffeinate -i $PY -I probes/intervencion/ablacion.py --paso correr # todo (reanudable)
  $PY -I probes/intervencion/ablacion.py --paso analizar
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "4")

import argparse
import json
import subprocess
import sys
import time

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
PROBES = os.path.dirname(AQUI)
for _p in (PROBES, os.path.join(PROBES, "nivel_b"), os.path.join(PROBES, "referencia")):
    sys.path.insert(0, _p)

MARCA = os.path.join(AQUI, "APROBADO_regla")
N_BOOT = 2000


# ---------------------------------------------------------------- datos

def cargar_pares(carpeta, indice):
    """Las filas de los pares, como en analizar_pares.main: sel (fila en las activaciones), y,
    g (archivo fuente, para las particiones), pares (infiel, fiel) y gp (origen de cada par)."""
    man = [json.loads(l) for l in open(os.path.join(carpeta, "manifiesto.jsonl"), encoding="utf-8")]
    ind = {r["id"]: r for r in map(json.loads, open(indice, encoding="utf-8"))}
    filas = [dict(ind[m["id"]], fila=j, grupo_man=m["grupo"]) for j, m in enumerate(man) if m["id"] in ind]
    tren = [r for r in filas if r["rol"] in ("infiel", "fiel")]
    sel = np.array([r["fila"] for r in tren])
    y = np.array([int(r["rol"] == "fiel") for r in tren])
    g_origen = np.array([r["grupo_man"] for r in tren])
    g = np.array([r.get("archivo") or r["grupo_man"] for r in tren])
    pos_de = {(r["par"], r["rol"]): k for k, r in enumerate(tren)}
    ids_par = sorted({r["par"] for r in tren})
    pares = np.array([[pos_de[(p, "infiel")], pos_de[(p, "fiel")]] for p in ids_par])
    gp = g_origen[pares[:, 0]]
    return tren, sel, y, g, pares, gp


def condiciones(k_azar):
    return ["base", "sonda", "solo_lean"] + [f"azar_{j:02d}" for j in range(k_azar)]


# ---------------------------------------------------------------- paso 1: direcciones

def paso_direcciones(a, carpeta, indice, salida):
    import probe_referencia as R
    from sklearn.preprocessing import StandardScaler
    import analizar_pares as AP

    meta = json.load(open(os.path.join(carpeta, "meta.json"), encoding="utf-8"))
    L1 = meta["n_capas_mas_embeddings"]
    capa = (2 * (L1 - 1)) // 3
    tren, sel, y, g, pares, gp = cargar_pares(carpeta, indice)
    Xc = R.acts(carpeta, "completo", "media_lean", sel)   # (n, L1, D)
    Xl = R.acts(carpeta, "solo_lean", "media_lean", sel)
    n, _, D = Xc.shape
    pliegues = R.particiones(y, g, 0)
    pliegue_de = np.full(n, -1)
    for k, (_, te) in enumerate(pliegues):
        pliegue_de[te] = k
    assert (pliegue_de >= 0).all()

    def direccion(X, tr):
        esc = StandardScaler().fit(X[tr, capa])
        m = R.lr().fit(esc.transform(X[tr, capa]), y[tr])
        w = m.coef_[0] / esc.scale_          # de vuelta al espacio de las activaciones
        return w / np.linalg.norm(w)

    azar = []
    for j in range(a.azar):
        v = np.random.default_rng(1000 + j).standard_normal(D)
        azar.append(v / np.linalg.norm(v))
    azar = np.array(azar)

    K = len(pliegues)
    D_sonda, D_lean = np.zeros((K, D)), np.zeros((K, D))
    M = np.zeros((K, 2 + a.azar, L1))        # medias por partición, condición (sonda, solo_lean, azar...) y capa
    oof = np.zeros(n)
    for k, (tr, te) in enumerate(pliegues):
        D_sonda[k], D_lean[k] = direccion(Xc, tr), direccion(Xl, tr)
        dirs = np.vstack([D_sonda[k], D_lean[k], azar])                    # (2+K_azar, D)
        M[k] = np.einsum("ncd,jd->jc", Xc[tr], dirs) / len(tr)
        oof[te] = Xc[te, capa] @ D_sonda[k]
    cosenos = [float(D_sonda[i] @ D_sonda[j]) for i in range(K) for j in range(i + 1, K)]
    info = {
        "modelo": a.nombre, "capa_fija": capa, "n_filas": int(n), "n_pares": int(len(pares)),
        "n_origenes": int(len(np.unique(gp))), "k_azar": a.azar,
        "coseno_entre_particiones_sonda": [round(min(cosenos), 4), round(max(cosenos), 4)],
        "coseno_sonda_solo_lean_por_particion": [round(float(D_sonda[k] @ D_lean[k]), 4) for k in range(K)],
        "coseno_max_abs_sonda_azar": round(float(np.abs(D_sonda @ azar.T).max()), 4) if a.azar else None,
        # la proyección fuera de partición sobre la dirección: cuánto separa los pares lo que se va a quitar
        "auroc_pareada_de_la_proyeccion_oof": round(AP.auc_p(oof, pares, gp), 4),
    }
    os.makedirs(salida, exist_ok=True)
    np.savez(os.path.join(salida, "direcciones.npz"), capa=capa, pliegue_de=pliegue_de, sel=sel,
             D_sonda=D_sonda, D_lean=D_lean, D_azar=azar, M=M)
    json.dump(info, open(os.path.join(salida, "direcciones.json"), "w", encoding="utf-8"),
              ensure_ascii=False, indent=2)
    print(json.dumps(info, ensure_ascii=False, indent=2))
    return info


# ---------------------------------------------------------------- paso 2: correr en el modelo

def localizar(modelo):
    """Devuelve (módulo de embeddings, lista de bloques). hidden_states[0] = salida de los embeddings;
    hidden_states[c] = salida del bloque c-1."""
    n = (getattr(modelo.config, "text_config", None) or modelo.config).num_hidden_layers
    for ruta in ("model.layers", "model.language_model.layers", "language_model.model.layers"):
        obj = modelo
        try:
            for parte in ruta.split("."):
                obj = getattr(obj, parte)
        except AttributeError:
            continue
        if len(obj) == n:
            return modelo.get_input_embeddings(), list(obj)
    raise SystemExit("No encuentro los bloques del modelo; revisa localizar().")


class Ablacion:
    """Ganchos que fijan, en los tokens marcados, la coordenada a lo largo de D[b] en M[b, capa].
    Un elemento del lote con D[b] = 0 queda intacto (la condición «base»)."""

    def __init__(self, modelo):
        import torch
        self.torch = torch
        self.D = self.M = self.mascara = None
        emb, bloques = localizar(modelo)
        # El último bloque no se toca: su salida pasa por la norma final antes de aparecer en
        # hidden_states (la media guardada de esa capa es posterior a la norma), y una intervención ahí,
        # sobre los tokens de Lean, ya no puede llegar al token de la respuesta.
        self.manijas = [emb.register_forward_hook(self._gancho(0))]
        self.manijas += [b.register_forward_hook(self._gancho(c + 1)) for c, b in enumerate(bloques[:-1])]

    def _gancho(self, c):
        def f(_mod, _inp, out):
            if self.D is None:
                return None
            h = out[0] if isinstance(out, tuple) else out
            hf = h.float()                                                       # (lote, tokens, D)
            coef = self.torch.einsum("btd,bd->bt", hf, self.D) - self.M[:, c][:, None]
            coef = coef * self.mascara[None, :]                                  # solo en los tokens de Lean
            h = (hf - coef[..., None] * self.D[:, None, :]).to(h.dtype)          # sin escrituras indexadas (MPS)
            return (h,) + tuple(out[1:]) if isinstance(out, tuple) else h
        return f

    def poner(self, D, M, mascara):
        self.D, self.M, self.mascara = D, M, mascara.float()

    def quitar(self):
        self.D = self.M = self.mascara = None

    def cerrar(self):
        for m in self.manijas:
            m.remove()


def mascara_lean(tok, prompt, c0, c1, torch):
    """La misma máscara de tokens de Lean que probes/extraer.py (incluida su salida por prefijo)."""
    enc = tok(prompt, return_offsets_mapping=True, add_special_tokens=False, return_tensors="pt")
    off = enc.pop("offset_mapping")[0]
    n = enc["input_ids"].shape[1]
    mascara = (off[:, 0] >= c0) & (off[:, 1] <= c1) & (off[:, 1] > off[:, 0])
    n0 = len(tok(prompt[:c0], add_special_tokens=False)["input_ids"])
    n1 = len(tok(prompt[:c1], add_special_tokens=False)["input_ids"])
    if abs(int(mascara.sum()) - (n1 - n0)) > 3:
        mascara = torch.zeros(n, dtype=torch.bool)
        mascara[min(n0, n):min(n1, n)] = True
    return enc["input_ids"], mascara


def paso_correr(a, carpeta, indice, salida):
    if not a.prueba and not os.path.exists(MARCA):
        sys.exit(f"Falta {os.path.relpath(MARCA, PROBES)} (la crea Carlos al aprobar la regla). "
                 "Sin ella solo corre --prueba N.")
    if not a.forzar:
        ocupado = subprocess.run(["pgrep", "-f", "probes/extraer.py|extraer_pares.py --candidatos|extraer_sin_pregunta.py"],
                                 capture_output=True).returncode == 0
        if ocupado:
            sys.exit("Ya hay una extracción en la GPU. Espera a que termine (o usa --forzar).")
    import pyarrow.parquet as pq
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    import extraer

    dir_ref = os.path.join(AQUI, "resultados", a.nombre)
    if not os.path.exists(os.path.join(dir_ref, "direcciones.npz")):
        sys.exit("Primero corre --paso direcciones.")
    z = np.load(os.path.join(dir_ref, "direcciones.npz"))
    meta = json.load(open(os.path.join(carpeta, "meta.json"), encoding="utf-8"))
    tren, sel, y, g, pares, gp = cargar_pares(carpeta, indice)
    assert (z["sel"] == sel).all(), "direcciones.npz no corresponde a este índice"
    k_azar = z["D_azar"].shape[0]
    conds = condiciones(k_azar)
    filas_pq = pq.read_table(os.path.join(os.path.dirname(indice), "pares_nivel_b.parquet")).to_pylist()

    filas_a_correr = np.arange(len(tren))
    if a.prueba:
        filas_a_correr = np.sort(pares[: a.prueba].ravel())
        conds = conds[:3] + conds[3:5]                     # base, sonda, solo_lean y dos al azar
    idx_cond = [condiciones(k_azar).index(c) for c in conds]

    os.makedirs(salida, exist_ok=True)
    ruta = os.path.join(salida, "pyes.npy")                # (condición, fila, [p_yes, p_no, logit_yes, logit_no])
    forma = (len(conds), len(tren), 4)
    P = np.lib.format.open_memmap(ruta, mode="r+" if os.path.exists(ruta) else "w+", dtype=np.float32, shape=forma)
    ruta_h = os.path.join(salida, "hecho.npy")
    hecho = np.load(ruta_h) if os.path.exists(ruta_h) else np.zeros(len(tren), dtype=bool)

    disp = "mps" if torch.backends.mps.is_available() else "cpu"
    tok = AutoTokenizer.from_pretrained(meta["modelo"], revision=meta["revision"])
    modelo = AutoModelForCausalLM.from_pretrained(
        meta["modelo"], revision=meta["revision"],
        dtype=getattr(torch, meta.get("dtype_modelo") or "bfloat16")).to(disp).eval()
    si_no = extraer.ids_si_no(tok)
    pre = tok(extraer.PREFIJO_RESPUESTA, add_special_tokens=False, return_tensors="pt")["input_ids"]
    chat = bool(meta.get("plantilla_chat", True))
    abl = Ablacion(modelo)

    # direcciones y medias por condición: (condición, partición, ...) -> se indexa con la partición de la fila
    Dz = np.zeros((len(conds), 5, z["D_sonda"].shape[1]), dtype=np.float32)
    Mz = np.zeros((len(conds), 5, z["M"].shape[2]), dtype=np.float32)
    for j, (c, ic) in enumerate(zip(conds, idx_cond)):
        if c == "base":
            continue
        Dz[j] = z["D_sonda"] if c == "sonda" else z["D_lean"] if c == "solo_lean" else z["D_azar"][ic - 3][None]
        Mz[j] = z["M"][:, ic - 1, :]
    Dt, Mt = torch.tensor(Dz, device=disp), torch.tensor(Mz, device=disp)

    def adelante(ids, mascara, k, quien):
        """Logits del último token para las condiciones «quien» (índices en conds), partición k."""
        abl.poner(Dt[quien, k], Mt[quien, k], mascara)
        try:
            with torch.no_grad():
                out = modelo(input_ids=ids.expand(len(quien), -1).to(disp), use_cache=False, logits_to_keep=1)
        finally:
            abl.quitar()
        return out.logits[:, -1].float()

    t0, hechas, comprobado = time.time(), 0, False
    for i in filas_a_correr:
        if hecho[i]:
            continue
        fila = filas_pq[tren[i]["id"]]
        prompt, (c0, c1) = extraer.construir_prompt(tok, fila, "completo", chat)
        ids, mascara = mascara_lean(tok, prompt, c0, c1, torch)
        ids2 = torch.cat([ids, pre], 1)
        mascara2 = torch.cat([mascara, torch.zeros(pre.shape[1], dtype=torch.bool)]).to(disp)
        k = int(z["pliegue_de"][i])
        if a.prueba and not comprobado:                    # comprobación de los ganchos, una vez
            comprobar_ganchos(modelo, abl, ids2.to(disp), mascara2, Dt[:, k], Mt[:, k], conds, torch)
            comprobado = True
        for ini in range(0, len(conds), a.lote):
            quien = list(range(ini, min(ini + a.lote, len(conds))))
            lg = adelante(ids2, mascara2, k, quien)
            pr = torch.softmax(lg, -1)
            P[quien, i] = torch.stack([pr[:, si_no[" Yes"]], pr[:, si_no[" No"]],
                                       lg[:, si_no[" Yes"]], lg[:, si_no[" No"]]], 1).cpu().numpy()
        hecho[i] = True
        hechas += 1
        if hechas % 25 == 0:
            P.flush()
            np.save(ruta_h, hecho)
            print(f"  {hechas} filas en esta sesión, {(time.time() - t0) / hechas:.2f} s/fila, "
                  f"faltan {int((~hecho[filas_a_correr]).sum())}", flush=True)
    P.flush()
    np.save(ruta_h, hecho)
    abl.cerrar()

    # Comprobaciones sin etiquetas: «base» frente al P(Yes) guardado, y cuánto mueve cada ablación la respuesta
    ok = hecho[filas_a_correr]
    f = filas_a_correr[ok]
    guardado = np.load(os.path.join(carpeta, "pyes_completo.npy"), mmap_mode="r")[sel[f]]
    dif_base = float(np.abs(P[0, f, 0] - guardado[:, 4]).max()) if len(f) else float("nan")
    margen = P[:, f, 2] - P[:, f, 3]                        # logit(Yes) - logit(No)
    mov = {c: round(float(np.abs(margen[j] - margen[0]).mean()), 4) for j, c in enumerate(conds)}
    resumen = {"filas_hechas": int(ok.sum()), "condiciones": conds, "lote": a.lote,
               "segundos_por_fila": round((time.time() - t0) / max(hechas, 1), 2),
               "base_vs_pyes_guardado_max_abs": round(dif_base, 5),
               "movimiento_medio_del_margen_logit": mov}
    json.dump(resumen, open(os.path.join(salida, "corrida.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(json.dumps(resumen, ensure_ascii=False, indent=2))
    print("Esperado: base_vs_pyes_guardado cerca de 0 (mismo prompt, sin intervenir) y un movimiento del "
          "margen mayor que 0 en las condiciones con ablación.")


def comprobar_ganchos(modelo, abl, ids, mascara, D, M, conds, torch):
    """En una fila: tras la ablación, la coordenada a lo largo de la dirección vale M en cada capa y
    en los tokens de Lean; «base» coincide con el modelo sin ganchos; antes del Lean nada cambia."""
    with torch.no_grad():
        libre = modelo(input_ids=ids, use_cache=False, output_hidden_states=True).hidden_states
        abl.poner(D, M, mascara)
        try:
            con = modelo(input_ids=ids.expand(D.shape[0], -1), use_cache=False, output_hidden_states=True).hidden_states
        finally:
            abl.quitar()
    primero = int(torch.nonzero(mascara)[0])
    queda = habia = err_base = err_antes = 0.0
    for c in range(len(con) - 1):                          # la última entrada va tras la norma final
        h, h0 = con[c].float(), libre[c][0].float()
        escala = float(h0.abs().max()) + 1e-9
        for b in range(1, D.shape[0]):
            queda += float(((h[b, mascara] @ D[b]) - M[b, c]).abs().mean())     # desvío que queda tras ablacionar
            habia += float(((h0[mascara] @ D[b]) - M[b, c]).abs().mean())       # desvío que había sin intervenir
        err_base = max(err_base, float((h[0] - h0).abs().max()) / escala)
        err_antes = max(err_antes, float((h[:, :primero] - h0[:primero]).abs().max()) / escala)
    resto = queda / max(habia, 1e-12)
    print(f"ganchos ({len(con) - 1} capas, {int(mascara.sum())} tokens de Lean): queda {100 * resto:.2f} % del desvío "
          f"a lo largo de las direcciones; base frente a sin ganchos {err_base:.5f} y cambio antes del Lean "
          f"{err_antes:.5f} (relativos al máximo de la capa)")
    if resto > 0.10 or err_antes > 0.05:
        sys.exit("Los ganchos no hacen lo que deben en este modelo. No sigo.")


# ---------------------------------------------------------------- paso 3: analizar

def paso_analizar(a, carpeta, indice, salida):
    if not os.path.exists(MARCA) and not a.sintetico:
        sys.exit(f"Falta {os.path.relpath(MARCA, PROBES)} (la crea Carlos al aprobar la regla). No analizo.")
    import analizar_pares as AP

    tren, sel, y, g, pares, gp = cargar_pares(carpeta, indice)
    P = np.load(os.path.join(salida, "pyes.npy"))
    hecho = np.load(os.path.join(salida, "hecho.npy"))
    if not hecho.all():
        sys.exit(f"Faltan {int((~hecho).sum())} filas por correr.")
    conds = condiciones(P.shape[0] - 3)
    S = P[:, :, 0] / np.maximum(P[:, :, 0] + P[:, :, 1], 1e-12)             # P(Yes) normalizado, por condición
    W = np.array([AP.por_origen(AP.w_pares(s, pares), gp) for s in S])       # (condición, origen)
    auc = W.mean(1)
    caida = auc[0] - auc
    az = np.arange(3, len(conds))
    rng = np.random.default_rng(0)
    m = W.shape[1]
    reps = np.array([W[:, rng.integers(0, m, m)].mean(1) for _ in range(N_BOOT)])   # (boot, condición)

    def ic(v):
        return [round(float(x), 4) for x in np.percentile(v, [2.5, 97.5])]

    d_azar = reps[:, az].mean(1) - reps[:, 1]              # caída(sonda) - media de caídas al azar
    d_lean = reps[:, 2] - reps[:, 1]                       # caída(sonda) - caída(solo_lean)
    mayor_que_todas = bool((caida[1] > caida[az]).all())
    out = {
        "modelo": a.nombre, "n_pares": int(len(pares)), "n_origenes": int(m), "k_azar": int(len(az)),
        "auroc_pareada_pyes": {c: round(float(auc[j]), 4) for j, c in enumerate(conds[:3])},
        "auroc_pareada_pyes_ic": {c: ic(reps[:, j]) for j, c in enumerate(conds[:3])},
        "auroc_pareada_pyes_azar": {"media": round(float(auc[az].mean()), 4), "min": round(float(auc[az].min()), 4),
                                    "max": round(float(auc[az].max()), 4)},
        "caida_sonda": [round(float(caida[1]), 4), *ic(reps[:, 0] - reps[:, 1])],
        "caida_solo_lean": [round(float(caida[2]), 4), *ic(reps[:, 0] - reps[:, 2])],
        "caida_azar": {"media": round(float(caida[az].mean()), 4), "max": round(float(caida[az].max()), 4)},
        "sonda_menos_media_azar": [round(float(caida[1] - caida[az].mean()), 4), *ic(d_azar)],
        "sonda_menos_solo_lean": [round(float(caida[1] - caida[2]), 4), *ic(d_lean)],
        "p_frente_a_azar": round(float((1 + (caida[az] >= caida[1]).sum()) / (len(az) + 1)), 4),
        "sonda_mayor_que_todas_las_de_azar": mayor_que_todas,
    }
    criterio = out["sonda_menos_media_azar"][1] > 0 and mayor_que_todas
    out["lectura"] = ("la ablación de la dirección de la sonda reduce la AUROC pareada de P(Yes) más que las "
                      "direcciones al azar" if criterio else
                      "no se establece que la ablación de la dirección de la sonda cambie P(Yes) más que una "
                      "dirección al azar")
    json.dump(out, open(os.path.join(salida, "ablacion.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paso", required=True, choices=["direcciones", "correr", "analizar"])
    ap.add_argument("--nombre", default="qwen3_4b")
    ap.add_argument("--azar", type=int, default=20, help="direcciones al azar (solo en --paso direcciones)")
    ap.add_argument("--lote", type=int, default=4, help="condiciones por pasada del modelo")
    ap.add_argument("--prueba", type=int, default=None, metavar="N", help="humo: N pares y 5 condiciones")
    ap.add_argument("--forzar", action="store_true", help="correr aunque haya otra extracción en la GPU")
    ap.add_argument("--sintetico", action="store_true", help=argparse.SUPPRESS)   # solo para probar «analizar»
    a = ap.parse_args()
    carpeta = os.path.join(PROBES, "activaciones", "nivel_b_" + a.nombre)
    indice = os.path.join(PROBES, "nivel_b", "datos", "pares_indice_principal.jsonl")
    base = os.path.join(AQUI, "resultados", a.nombre)
    if a.paso == "direcciones":
        paso_direcciones(a, carpeta, indice, base)
    elif a.paso == "correr":
        paso_correr(a, carpeta, indice, base + (f"_prueba{a.prueba}" if a.prueba else ""))
    else:
        paso_analizar(a, carpeta, indice, base)


if __name__ == "__main__":
    main()
