"""S5. Desplazar cada fila hacia la clase contraria a lo largo de la diferencia de medias (11 nov 2026).

POR QUÉ. La ablación S4 quitó UNA dirección (la de la regresión logística en la capa 24) en todas las
capas y no movió el P(Yes) más que una dirección al azar. Tenía dos límites. En las demás capas la
etiqueta vive en otras direcciones, y además fijaba la coordenada de todos los tokens en una constante,
con lo que borraba mucha variación entre ítems que nada tiene que ver con la clase: en la capa fija la
mitad de la distancia entre clases (h) es unas 0,15 desviaciones típicas dentro de clase. Aquí cada capa
usa su propia dirección y la intervención mueve solo la MEDIA sobre los tokens de Lean, que es lo que
lee la segunda lectura, sin tocar la variación entre tokens ni entre ítems.

QUÉ SE HACE.
  direcciones (CPU)
      Para cada partición (cinco, por archivo fuente, semilla 0) y cada capa c, con las activaciones
      guardadas («completo», media sobre los tokens de Lean) de las filas de entrenamiento:
        u_c   dirección unitaria de la diferencia de medias (adecuadas − inadecuadas)
        g_c   coordenada media a lo largo de u_c
        h_c   la mitad de la distancia entre las dos medias de clase a lo largo de u_c
      Lo mismo con «solo_lean» (control de especificidad) y con 20 direcciones al azar (control de
      tamaño). Los controles usan el mismo h_c, así que el desplazamiento tiene la misma magnitud.
  correr (GPU)
      Prompt normal, con la pregunta. Por fila, una pasada limpia da m_c, la coordenada media sobre los
      tokens de Lean a lo largo de cada dirección. Luego, en los embeddings y en la salida de cada bloque
      menos el último, se suma a TODOS los tokens de Lean el mismo múltiplo de la dirección, el justo
      para que la coordenada media quede en un objetivo:
        desplazar   m_c + f * s * h_c,  s = +1 si la fila es inadecuada y −1 si es adecuada.
                    f = 2 es la distancia completa entre las medias de clase (principal); f = 4 y 8, dosis.
                    f = 0 es el placebo: los ganchos trabajan, el objetivo es la coordenada limpia.
        pareja      m_c + (coordenada guardada de su pareja − la suya): el par mínimo intercambia su
                    coordenada.
        borrar      g_c para todas las filas: la media deja de distinguir ítems a lo largo de u_c.
      El objetivo se fija capa por capa, así que el desplazamiento no se acumula. Se lee P(Yes) tras
      «**Answer:».
  analizar (CPU)
      AUROC pareada de P(Yes) por condición. Si la respuesta del modelo usa ese eje, desplazar (f = 2)
      debe bajarla más que el mismo desplazamiento a lo largo de direcciones al azar.

No modifica nada existente. «correr» completo y «analizar» exigen probes/intervencion/APROBADO_regla_S5
con el SHA-256 de probes/intervencion/regla_S5.md.

Uso (desde la raíz de Proyecto Godel; PY=biblioteca/.venv/bin/python):
  $PY -I probes/intervencion/intercambio.py --paso direcciones
  HF_HUB_OFFLINE=1 $PY -I probes/intervencion/intercambio.py --paso correr --prueba 4
  HF_HUB_OFFLINE=1 caffeinate -i $PY -I probes/intervencion/intercambio.py --paso correr
  $PY -I probes/intervencion/intercambio.py --paso analizar
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "VECLIB_MAXIMUM_THREADS"):
    os.environ.setdefault(_v, "4")

import argparse
import hashlib
import json
import subprocess
import sys
import time

import numpy as np

AQUI = os.path.dirname(os.path.abspath(__file__))
PROBES = os.path.dirname(AQUI)
for _p in (AQUI, PROBES, os.path.join(PROBES, "nivel_b"), os.path.join(PROBES, "referencia")):
    sys.path.insert(0, _p)

MARCA = os.path.join(AQUI, "APROBADO_regla_S5")
REGLA = os.path.join(AQUI, "regla_S5.md")
N_BOOT = 2000
N_AZAR = 20                                  # direcciones al azar por capa
K_PRINCIPAL, K_BORRAR, K_OTROS = 20, 10, 5   # cuántas se usan en cada familia de condiciones
DOSIS = (4, 8)


def condiciones():
    """(nombre, índice de dirección o None, modo, f). Direcciones: 0 = sonda (diferencia de medias en
    «completo»), 1 = solo_lean, 2 + j = azar j. Modos: «desp» (m + f*s*h), «pareja», «media» (g)."""
    c = [("base", None, None, 0.0), ("placebo", 0, "desp", 0.0),
         ("desp2_sonda", 0, "desp", 2.0), ("desp2_solo_lean", 1, "desp", 2.0),
         ("pareja_sonda", 0, "pareja", 0.0),
         ("borrar_sonda", 0, "media", 0.0), ("borrar_solo_lean", 1, "media", 0.0)]
    c += [(f"desp{f}_sonda", 0, "desp", float(f)) for f in DOSIS]
    c += [(f"desp2_azar_{j:02d}", 2 + j, "desp", 2.0) for j in range(K_PRINCIPAL)]
    for f in DOSIS:
        c += [(f"desp{f}_azar_{j:02d}", 2 + j, "desp", float(f)) for j in range(K_OTROS)]
    c += [(f"pareja_azar_{j:02d}", 2 + j, "pareja", 0.0) for j in range(K_OTROS)]
    c += [(f"borrar_azar_{j:02d}", 2 + j, "media", 0.0) for j in range(K_BORRAR)]
    return c


def condiciones_prueba():
    c = condiciones()
    return c[:7] + [x for x in c if x[0] in ("desp8_sonda", "desp2_azar_00")]


def exigir_marca():
    if not os.path.exists(MARCA):
        sys.exit("Falta probes/intervencion/APROBADO_regla_S5 (la crea Carlos). Sin ella solo corre --prueba N.")
    if hashlib.sha256(open(REGLA, "rb").read()).hexdigest() not in open(MARCA, encoding="utf-8").read():
        sys.exit("regla_S5.md cambió después de aprobarse (su SHA-256 no está en la marca). No corro.")


def rutas(nombre):
    return (os.path.join(PROBES, "activaciones", "nivel_b_" + nombre),
            os.path.join(PROBES, "nivel_b", "datos", "pares_indice_principal.jsonl"),
            os.path.join(AQUI, "resultados_s5", nombre))


# ---------------------------------------------------------------- paso 1

def paso_direcciones(a):
    import ablacion as A
    import analizar_pares as AP
    import probe_referencia as R
    carpeta, indice, salida = rutas(a.nombre)
    meta = json.load(open(os.path.join(carpeta, "meta.json"), encoding="utf-8"))
    L1 = meta["n_capas_mas_embeddings"]
    capa = (2 * (L1 - 1)) // 3
    tren, sel, y, g, pares, gp = A.cargar_pares(carpeta, indice)
    Xc = R.acts(carpeta, "completo", "media_lean", sel)
    Xl = R.acts(carpeta, "solo_lean", "media_lean", sel)
    n, _, D = Xc.shape
    assert len(np.unique(pares)) == n == 2 * len(pares), "cada fila debe estar en un par y solo en uno"
    pareja = np.zeros(n, dtype=int)
    pareja[pares[:, 0]], pareja[pares[:, 1]] = pares[:, 1], pares[:, 0]
    pliegues = R.particiones(y, g, 0)
    pliegue_de = np.full(n, -1)
    for k, (_, te) in enumerate(pliegues):
        pliegue_de[te] = k
    n_dir = 2 + N_AZAR
    azar = np.zeros((N_AZAR, L1, D), dtype=np.float32)
    for j in range(N_AZAR):
        v = np.random.default_rng(2000 + j).standard_normal((L1, D))
        azar[j] = v / np.linalg.norm(v, axis=1, keepdims=True)

    def unitaria(X, tr):
        d = X[tr][y[tr] == 1].mean(0) - X[tr][y[tr] == 0].mean(0)             # (L1, D)
        nrm = np.linalg.norm(d, axis=1, keepdims=True)
        return d / np.maximum(nrm, 1e-12), nrm[:, 0]

    K = len(pliegues)
    U = np.zeros((n_dir, K, L1, D), dtype=np.float32)
    G = np.zeros((n_dir, K, L1), dtype=np.float32)      # coordenada media (sobre «completo») a lo largo de cada dirección
    H = np.zeros((K, L1), dtype=np.float32)             # mitad de la distancia entre medias de clase (dirección de la sonda)
    Cg = np.zeros((n_dir, n, L1), dtype=np.float32)     # coordenada guardada de cada fila, con las direcciones de su partición
    Dpar = np.zeros((n_dir, n, L1), dtype=np.float32)   # coordenada de la pareja menos la propia
    oof, oof_borrado = np.zeros(n), np.zeros(n)
    h_sobre_sd = np.zeros((K, L1))                      # tamaño de h en desviaciones típicas dentro de clase
    for k, (tr, te) in enumerate(pliegues):
        U[0, k], norma = unitaria(Xc, tr)
        U[1, k], _ = unitaria(Xl, tr)
        U[2:, k] = azar
        H[k] = norma / 2
        G[:, k] = np.einsum("ncd,jcd->jc", Xc[tr], U[:, k]) / len(tr)
        Cg[:, te] = np.einsum("ncd,jcd->jnc", Xc[te], U[:, k])
        Dpar[:, te] = np.einsum("ncd,jcd->jnc", Xc[pareja[te]] - Xc[te], U[:, k])
        z = np.einsum("ncd,cd->nc", Xc[tr], U[0, k])
        intra = np.sqrt((z[y[tr] == 1].var(0) + z[y[tr] == 0].var(0)) / 2)
        h_sobre_sd[k] = H[k] / np.maximum(intra, 1e-12)
        u = U[0, k, capa]
        oof[te] = Xc[te, capa] @ u
        # comprobación: tras llevar la coordenada a la media, una sonda nueva en la capa fija ya no separa
        borra = lambda X: X - np.outer(X @ u - G[0, k, capa], u)
        oof_borrado[te] = R.ajustar_predecir(borra(Xc[tr, capa]), y[tr], borra(Xc[te, capa]))
    s = np.where(y == 0, 1.0, -1.0)
    info = {
        "modelo": a.nombre, "capa_fija": int(capa), "n_filas": int(n), "n_pares": int(len(pares)),
        "n_origenes": int(len(np.unique(gp))), "condiciones": len(condiciones()),
        "parejas_en_la_misma_particion": float((pliegue_de[pares[:, 0]] == pliegue_de[pares[:, 1]]).mean()),
        "auroc_pareada_proyeccion_diferencia_de_medias_capa_fija": round(AP.auc_p(oof, pares, gp), 4),
        "auroc_pareada_sonda_nueva_tras_borrar_en_capa_fija": round(AP.auc_p(oof_borrado, pares, gp), 4),
        "nota_sonda_nueva": "cercana a 0.5 por construcción: al igualar las medias de clase ninguna sonda lineal "
                            "separa en entrenamiento; solo comprueba que el borrado hace lo que dice",
        "coseno_sonda_solo_lean_capa_fija": [round(float(U[0, k, capa] @ U[1, k, capa]), 4) for k in range(K)],
        "norma_media_activacion_capa_fija": round(float(np.linalg.norm(Xc[:, capa], axis=1).mean()), 2),
        "h_capa_fija": round(float(H[:, capa].mean()), 3),
        "h_en_desviaciones_tipicas_dentro_de_clase": {"capa_fija": round(float(h_sobre_sd[:, capa].mean()), 3),
                                                      "minimo_entre_capas": round(float(h_sobre_sd.mean(0).min()), 3),
                                                      "maximo_entre_capas": round(float(h_sobre_sd.mean(0).max()), 3)},
        "diferencia_de_pareja_en_unidades_de_h_capa_fija": {
            "sonda_media_firmada": round(float((s * Dpar[0, :, capa] / H[pliegue_de, capa]).mean()), 3),
            "azar_media_absoluta": round(float((np.abs(Dpar[2:, :, capa]) / H[pliegue_de, capa]).mean()), 3)},
        "h_por_capa_particion_0": [round(float(x), 3) for x in H[0]],
    }
    os.makedirs(salida, exist_ok=True)
    np.savez(os.path.join(salida, "direcciones.npz"), capa=capa, pliegue_de=pliegue_de, sel=sel, y=y, pareja=pareja,
             U=U, G=G, H=H, Cg=Cg, Dpar=Dpar)
    json.dump(info, open(os.path.join(salida, "direcciones.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(json.dumps(info, ensure_ascii=False, indent=2))
    return info


# ---------------------------------------------------------------- paso 2

class Desplazar:
    """Ganchos: en la capa c suma a todos los tokens marcados el mismo múltiplo de D[b, c], el justo para
    que la coordenada MEDIA sobre esos tokens quede en T[b, c]. La variación entre tokens no cambia.
    Un elemento del lote con D = 0 queda intacto. El último bloque no se toca (su salida pasa por la norma
    final, y ahí una intervención sobre los tokens de Lean ya no llega al token de la respuesta)."""

    def __init__(self, modelo):
        import ablacion as A
        import torch
        self.torch = torch
        self.D = self.T = self.mascara = None
        emb, bloques = A.localizar(modelo)
        # prepend: transformers recoge hidden_states con ganchos propios; los nuestros van antes, para que
        # lo que se recoge (y lo que mira comprobar_ganchos) sea ya el estado intervenido.
        self.manijas = [emb.register_forward_hook(self._gancho(0), prepend=True)]
        self.manijas += [b.register_forward_hook(self._gancho(c + 1), prepend=True) for c, b in enumerate(bloques[:-1])]

    def _gancho(self, c):
        def f(_mod, _inp, out):
            if self.D is None:
                return None
            h = out[0] if isinstance(out, tuple) else out
            hf = h.float()
            d = self.D[:, c]                                                      # (lote, D)
            coef = self.torch.einsum("btd,bd->bt", hf, d) * self.mascara[None, :]
            media = coef.sum(1) / self.n_lean                                     # coordenada media actual
            paso = (self.T[:, c] - media)[:, None] * self.mascara[None, :]        # (lote, tokens); 0 fuera del Lean
            h = (hf + paso[..., None] * d[:, None, :]).to(h.dtype)                # sin escrituras indexadas (MPS)
            return (h,) + tuple(out[1:]) if isinstance(out, tuple) else h
        return f

    def poner(self, D, T, mascara):
        self.D, self.T, self.mascara = D, T, mascara.float()
        self.n_lean = self.mascara.sum()

    def quitar(self):
        self.D = self.T = self.mascara = None

    def cerrar(self):
        for m in self.manijas:
            m.remove()


def comprobar_ganchos(modelo, gan, ids, mascara, D, T, torch):
    """En un lote real: la coordenada media queda en el objetivo, «base» no se mueve y nada cambia antes
    del primer token de Lean."""
    with torch.no_grad():
        libre = modelo(input_ids=ids, use_cache=False, output_hidden_states=True).hidden_states
        gan.poner(D, T, mascara)
        try:
            con = modelo(input_ids=ids.expand(D.shape[0], -1), use_cache=False, output_hidden_states=True).hidden_states
        finally:
            gan.quitar()
    primero = int(torch.nonzero(mascara)[0])
    queda = habia = err_base = err_antes = 0.0
    activos = [b for b in range(D.shape[0]) if float(D[b].abs().sum()) > 0]
    for c in range(len(con) - 1):
        h, h0 = con[c].float(), libre[c][0].float()
        escala = float(h0.abs().max()) + 1e-9
        for b in activos:
            queda += abs(float((h[b, mascara] @ D[b, c]).mean() - T[b, c]))
            habia += abs(float((h0[mascara] @ D[b, c]).mean() - T[b, c]))
        err_base = max(err_base, float((h[0] - h0).abs().max()) / escala)
        err_antes = max(err_antes, float((h[:, :primero] - h0[:primero]).abs().max()) / escala)
    resto = queda / max(habia, 1e-12)
    print(f"ganchos ({len(con) - 1} capas, {int(mascara.sum())} tokens de Lean, {len(activos)} condiciones con dirección): "
          f"queda {100 * resto:.2f} % de la distancia al objetivo; base frente a sin ganchos {err_base:.5f} y "
          f"cambio antes del Lean {err_antes:.5f} (relativos al máximo de la capa)", flush=True)
    if resto > 0.10 or err_antes > 0.05:
        sys.exit("Los ganchos no hacen lo que deben en este modelo. No sigo.")


def paso_correr(a):
    import ablacion as A
    carpeta, indice, base = rutas(a.nombre)
    salida = base + (f"_prueba{a.prueba}" if a.prueba else "")
    if not a.prueba:
        exigir_marca()
    if not a.forzar and subprocess.run(
            ["pgrep", "-f", "probes/extraer.py|extraer_pares.py --candidatos|extraer_sin_pregunta.py|ablacion.py --paso correr"],
            capture_output=True).returncode == 0:
        sys.exit("Ya hay otra corrida en la GPU. Espera a que termine (o usa --forzar).")
    import pyarrow.parquet as pq
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer
    import extraer

    if not os.path.exists(os.path.join(base, "direcciones.npz")):
        sys.exit("Primero corre --paso direcciones.")
    z = np.load(os.path.join(base, "direcciones.npz"))
    meta = json.load(open(os.path.join(carpeta, "meta.json"), encoding="utf-8"))
    tren, sel, y, g, pares, gp = A.cargar_pares(carpeta, indice)
    assert (z["sel"] == sel).all() and (z["y"] == y).all(), "direcciones.npz no corresponde a este índice"
    conds = condiciones_prueba() if a.prueba else condiciones()
    filas_a_correr = np.sort(pares[: a.prueba].ravel()) if a.prueba else np.arange(len(tren))
    filas_pq = pq.read_table(os.path.join(os.path.dirname(indice), "pares_nivel_b.parquet")).to_pylist()

    os.makedirs(salida, exist_ok=True)
    ruta = os.path.join(salida, "pyes.npy")
    if os.path.exists(ruta) and np.load(ruta, mmap_mode="r").shape != (len(conds), len(tren), 4):
        sys.exit(f"{ruta} es de otra lista de condiciones. Muévelo o bórralo antes de seguir.")
    P = np.lib.format.open_memmap(ruta, mode="r+" if os.path.exists(ruta) else "w+", dtype=np.float32,
                                  shape=(len(conds), len(tren), 4))
    ruta_h, ruta_v = os.path.join(salida, "hecho.npy"), os.path.join(salida, "viva_vs_guardada.npy")
    reanuda = not a.prueba                      # el humo empieza siempre de cero, para que compruebe los ganchos
    hecho = np.load(ruta_h) if reanuda and os.path.exists(ruta_h) else np.zeros(len(tren), dtype=bool)
    viva = np.load(ruta_v) if reanuda and os.path.exists(ruta_v) else np.full(len(tren), np.nan, dtype=np.float32)
    json.dump([c[0] for c in conds], open(os.path.join(salida, "condiciones.json"), "w"))

    disp = "mps" if torch.backends.mps.is_available() else "cpu"
    tok = AutoTokenizer.from_pretrained(meta["modelo"], revision=meta["revision"])
    modelo = AutoModelForCausalLM.from_pretrained(
        meta["modelo"], revision=meta["revision"],
        dtype=getattr(torch, meta.get("dtype_modelo") or "bfloat16")).to(disp).eval()
    si_no = extraer.ids_si_no(tok)
    pre = tok(extraer.PREFIJO_RESPUESTA, add_special_tokens=False, return_tensors="pt")["input_ids"]
    chat = bool(meta.get("plantilla_chat", True))
    gan = Desplazar(modelo)
    U, G, H = (torch.tensor(z[k], device=disp) for k in ("U", "G", "H"))
    Cg, Dpar = z["Cg"], torch.tensor(z["Dpar"], device=disp)
    capa = int(z["capa"])
    L1, Dm = U.shape[2], U.shape[3]

    def tensores(i, k, signo, m):
        """D (condición, capa, D) y objetivo T (condición, capa) para la fila i; m = coordenadas limpias (dirección, capa)."""
        D = torch.zeros((len(conds), L1, Dm), device=disp)
        T = torch.zeros((len(conds), L1), device=disp)
        for j, (_, d, modo, f) in enumerate(conds):
            if d is None:
                continue
            D[j] = U[d, k]
            T[j] = {"desp": lambda: m[d] + f * signo * H[k],
                    "pareja": lambda: m[d] + Dpar[d, i],
                    "media": lambda: G[d, k]}[modo]()
        return D, T

    t0, hechas, comprobado = time.time(), 0, False
    for i in filas_a_correr:
        if hecho[i]:
            continue
        fila = filas_pq[tren[i]["id"]]
        prompt, (c0, c1) = extraer.construir_prompt(tok, fila, "completo", chat)
        ids, mascara = A.mascara_lean(tok, prompt, c0, c1, torch)
        ids2 = torch.cat([ids, pre], 1).to(disp)
        mascara2 = torch.cat([mascara, torch.zeros(pre.shape[1], dtype=torch.bool)]).to(disp)
        k = int(z["pliegue_de"][i])
        with torch.no_grad():                               # pasada limpia: coordenada media sobre el Lean, por capa
            hs = modelo(input_ids=ids2, use_cache=False, output_hidden_states=True).hidden_states
            mf = mascara2.float()
            limpia = torch.stack([(h[0].float() * mf[:, None]).sum(0) / mf.sum() for h in hs])      # (L1, D)
            m = torch.einsum("cd,jcd->jc", limpia, U[:, k])                                        # (dirección, L1)
        del hs
        viva[i] = abs(float(m[0, capa]) - float(Cg[0, i, capa])) / float(H[k, capa])
        D, T = tensores(i, k, 1.0 if y[i] == 0 else -1.0, m)        # inadecuada: hacia la media de las adecuadas
        if a.prueba and not comprobado:
            q = list(range(min(len(conds), 8)))
            comprobar_ganchos(modelo, gan, ids2, mascara2, D[q], T[q], torch)
            comprobado = True
        for ini in range(0, len(conds), a.lote):
            q = list(range(ini, min(ini + a.lote, len(conds))))
            gan.poner(D[q], T[q], mascara2)
            try:
                with torch.no_grad():
                    lg = modelo(input_ids=ids2.expand(len(q), -1), use_cache=False,
                                logits_to_keep=1).logits[:, -1].float()
            finally:
                gan.quitar()
            pr = torch.softmax(lg, -1)
            P[q, i] = torch.stack([pr[:, si_no[" Yes"]], pr[:, si_no[" No"]],
                                   lg[:, si_no[" Yes"]], lg[:, si_no[" No"]]], 1).cpu().numpy()
        hecho[i] = True
        hechas += 1
        if hechas % 25 == 0:
            P.flush()
            np.save(ruta_h, hecho)
            np.save(ruta_v, viva)
            falta = int((~hecho[filas_a_correr]).sum())
            spf = (time.time() - t0) / hechas
            print(f"  {hechas} filas en esta sesión, {spf:.1f} s/fila, faltan {falta} (unos {falta * spf / 60:.0f} min)", flush=True)
    P.flush()
    np.save(ruta_h, hecho)
    np.save(ruta_v, viva)
    gan.cerrar()

    f = filas_a_correr[hecho[filas_a_correr]]
    guardado = np.load(os.path.join(carpeta, "pyes_completo.npy"), mmap_mode="r")[sel[f]]
    margen = P[:, f, 2] - P[:, f, 3]
    nombres = [c[0] for c in conds]
    mov = {n: round(float(np.abs(margen[j] - margen[0]).mean()), 4) for j, n in enumerate(nombres)}
    resumen = {"filas_hechas": int(len(f)), "condiciones": len(conds), "lote": a.lote,
               "segundos_por_fila": round((time.time() - t0) / max(hechas, 1), 2),
               "base_vs_pyes_guardado_max_abs": round(float(np.abs(P[0, f, 0] - guardado[:, 4]).max()), 5) if len(f) else None,
               "coordenada_viva_vs_guardada_capa_fija_en_h": {"mediana": round(float(np.nanmedian(viva[f])), 4),
                                                               "maximo": round(float(np.nanmax(viva[f])), 4)} if len(f) else None,
               "ruido_de_los_ganchos_placebo_vs_base": mov.get("placebo"),
               "movimiento_medio_del_margen_logit": mov}
    json.dump(resumen, open(os.path.join(salida, "corrida.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(json.dumps(resumen, ensure_ascii=False, indent=2))
    print("Esperado: placebo muy por debajo de las condiciones que desplazan (es el ruido numérico de los ganchos) y "
          "coordenada viva frente a guardada muy por debajo de 1 (en unidades de h).")


# ---------------------------------------------------------------- paso 3

def paso_analizar(a):
    import ablacion as A
    import analizar_pares as AP
    if not a.sintetico:
        exigir_marca()
    carpeta, indice, salida = rutas(a.nombre)
    tren, sel, y, g, pares, gp = A.cargar_pares(carpeta, indice)
    P = np.load(os.path.join(salida, "pyes.npy"))
    hecho = np.load(os.path.join(salida, "hecho.npy"))
    if not hecho.all():
        sys.exit(f"Faltan {int((~hecho).sum())} filas por correr.")
    nombres = [c[0] for c in condiciones()]
    assert P.shape[0] == len(nombres)
    j = {n: k for k, n in enumerate(nombres)}
    az = lambda pref: [j[n] for n in nombres if n.startswith(pref + "_azar")]

    # AUROC pareada de P(Yes) por condición, con remuestreo por origen
    S = P[:, :, 0] / np.maximum(P[:, :, 0] + P[:, :, 1], 1e-12)
    W = np.array([AP.por_origen(AP.w_pares(s, pares), gp) for s in S])            # (condición, origen)
    # desplazamiento firmado del margen: positivo = la respuesta se movió hacia la clase contraria
    margen = P[:, :, 2] - P[:, :, 3]
    s = np.where(y == 0, 1.0, -1.0)
    firm = s[None, :] * (margen - margen[0][None, :])
    F = np.array([AP.por_origen((v[pares[:, 0]] + v[pares[:, 1]]) / 2, gp) for v in firm])
    auc, fmed = W.mean(1), F.mean(1)
    rng = np.random.default_rng(0)
    m = W.shape[1]
    idx = rng.integers(0, m, (N_BOOT, m))
    rW = np.array([W[:, ix].mean(1) for ix in idx])                               # (réplica, condición)
    rF = np.array([F[:, ix].mean(1) for ix in idx])
    ic = lambda v: [round(float(x), 4) for x in np.percentile(v, [2.5, 97.5])]
    caida = auc[0] - auc

    def frente_a_azar(cond, azar):
        c = j[cond]
        return {"auroc": round(float(auc[c]), 4), "ic_auroc": ic(rW[:, c]),
                "caida": [round(float(caida[c]), 4), *ic(rW[:, 0] - rW[:, c])],
                "caida_azar_media": round(float(caida[azar].mean()), 4),
                "caida_azar_max": round(float(caida[azar].max()), 4),
                "caida_menos_media_azar": [round(float(caida[c] - caida[azar].mean()), 4),
                                           *ic(rW[:, azar].mean(1) - rW[:, c])],
                "mayor_que_todas_las_de_azar": bool((caida[c] > caida[azar]).all()),
                "p_frente_a_azar": round(float((1 + (caida[azar] >= caida[c]).sum()) / (len(azar) + 1)), 4),
                "margen_firmado": [round(float(fmed[c]), 4), *ic(rF[:, c])],
                "margen_firmado_azar_media": round(float(fmed[azar].mean()), 4),
                "margen_firmado_azar_max": round(float(fmed[azar].max()), 4),
                "margen_firmado_menos_media_azar": [round(float(fmed[c] - fmed[azar].mean()), 4),
                                                    *ic(rF[:, c] - rF[:, azar].mean(1))],
                "p_margen_frente_a_azar": round(float((1 + (fmed[azar] >= fmed[c]).sum()) / (len(azar) + 1)), 4)}

    sl, so = j["desp2_solo_lean"], j["desp2_sonda"]
    out = {
        "modelo": a.nombre, "n_pares": int(len(pares)), "n_origenes": int(m),
        "base": {"auroc": round(float(auc[0]), 4), "ic": ic(rW[:, 0])},
        "placebo": {"auroc": round(float(auc[j["placebo"]]), 4),
                    "movimiento_medio_del_margen": round(float(np.abs(margen[j["placebo"]] - margen[0]).mean()), 4)},
        "principal_desplazar_f2": frente_a_azar("desp2_sonda", az("desp2")),
        **{f"dosis_f{f}": frente_a_azar(f"desp{f}_sonda", az(f"desp{f}")) for f in DOSIS},
        "pareja": frente_a_azar("pareja_sonda", az("pareja")),
        "borrar": frente_a_azar("borrar_sonda", az("borrar")),
        "control_solo_lean": {
            "desplazar_f2_auroc": round(float(auc[sl]), 4), "borrar_auroc": round(float(auc[j["borrar_solo_lean"]]), 4),
            "caida_sonda_menos_solo_lean_f2": [round(float(caida[so] - caida[sl]), 4), *ic(rW[:, sl] - rW[:, so])],
            "margen_firmado_f2": [round(float(fmed[sl]), 4), *ic(rF[:, sl])],
            "margen_firmado_sonda_menos_solo_lean_f2": [round(float(fmed[so] - fmed[sl]), 4), *ic(rF[:, so] - rF[:, sl])]},
        "nota": "f se mide en unidades de h (mitad de la distancia entre medias de clase, por capa); los controles al "
                "azar reciben el mismo desplazamiento. Las dosis, la pareja y el borrado son secundarios y descriptivos.",
    }
    p = out["principal_desplazar_f2"]
    ok = p["caida_menos_media_azar"][1] > 0 and p["mayor_que_todas_las_de_azar"]
    out["criterio_principal_cumplido"] = bool(ok)
    out["lectura"] = ("desplazar cada fila hacia la clase contraria a lo largo de la diferencia de medias reduce la AUROC "
                      "pareada de P(Yes) más que el mismo desplazamiento a lo largo de direcciones al azar" if ok else
                      "no se establece que desplazar a lo largo de la diferencia de medias cambie P(Yes) más que el "
                      "mismo desplazamiento a lo largo de una dirección al azar")
    json.dump(out, open(os.path.join(salida, "s5.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(json.dumps(out, ensure_ascii=False, indent=2))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--paso", required=True, choices=["direcciones", "correr", "analizar"])
    ap.add_argument("--nombre", default="qwen3_4b")
    ap.add_argument("--lote", type=int, default=4)
    ap.add_argument("--prueba", type=int, default=None, metavar="N", help="humo: N pares y 9 condiciones")
    ap.add_argument("--forzar", action="store_true")
    ap.add_argument("--sintetico", action="store_true", help=argparse.SUPPRESS)
    a = ap.parse_args()
    {"direcciones": paso_direcciones, "correr": paso_correr, "analizar": paso_analizar}[a.paso](a)


if __name__ == "__main__":
    main()
