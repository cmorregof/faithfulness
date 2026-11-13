"""Control del prerregistro v2 (§7, §9.9): línea base de embeddings de texto con BAAI/bge-m3 (MIT).

Embedding denso de bge-m3 (CLS de la última capa, normalizado L2) de los textos de «completo»
(PLANTILLA_COMPLETO de extraer.py, sin plantilla de chat) y de «solo_lean», sobre las 450 filas
que compilan. Después, el mismo probe (StandardScaler + LR C = 1) con las mismas particiones (5
semillas, OOF promediados) y bootstrap de grupos: AUROC(completo), AUROC(solo Lean) y Δ.

Uso: biblioteca/.venv/bin/python -I probes/referencia/embeddings_base.py [--dispositivo mps]
"""
import argparse
import importlib.util
import json
import os
import sys
import time

import numpy as np
import torch

AQUI = os.path.dirname(os.path.abspath(__file__))
RAIZ = os.path.dirname(os.path.dirname(AQUI))
sys.path.insert(0, os.path.join(RAIZ, "probes"))
import extraer as E  # noqa: E402  (solo las plantillas)

_spec = importlib.util.spec_from_file_location("probe_referencia", os.path.join(AQUI, "probe_referencia.py"))
ref = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ref)

MODELO, REVISION = "BAAI/bge-m3", "5617a9f61b028005a4858fdac845db406aefb181"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dispositivo", default="mps" if torch.backends.mps.is_available() else "cpu")
    ap.add_argument("--salida", default=os.path.join(RAIZ, "probes", "activaciones", "bge_m3"))
    a = ap.parse_args()
    os.makedirs(a.salida, exist_ok=True)
    os.environ["HF_HUB_OFFLINE"] = "1"
    from transformers import AutoModel, AutoTokenizer
    t0 = time.time()
    carpeta_q = os.path.join(RAIZ, "probes", "activaciones", "qwen3_4b")
    man, _, filas = ref.cargar(carpeta_q)
    man = [m for m in man if m["compila"] == 1]
    idx = np.array([m["idx"] for m in man]); y = np.array([m["etiqueta"] for m in man])
    g = np.array([m["grupo"] for m in man])
    tok = AutoTokenizer.from_pretrained(MODELO, revision=REVISION)
    mod = AutoModel.from_pretrained(MODELO, revision=REVISION).to(a.dispositivo).eval()
    textos = {
        "completo": [E.PLANTILLA_COMPLETO.format(nl=filas[i]["refined_statement"].strip(),
                                                 lean=filas[i]["autoformalization"].strip()) for i in idx],
        "solo_lean": [E.PLANTILLA_SOLO_LEAN.format(lean=filas[i]["autoformalization"].strip()) for i in idx]}
    emb, truncados = {}, {}
    for v, ts in textos.items():
        out = []
        tr = 0
        for t in ts:
            enc = tok(t, return_tensors="pt", truncation=True, max_length=8192)
            tr += int(len(tok(t)["input_ids"]) > 8192)
            with torch.no_grad():
                h = mod(**{k: x.to(a.dispositivo) for k, x in enc.items()}).last_hidden_state[0, 0]
            out.append(torch.nn.functional.normalize(h.float(), dim=-1).cpu().numpy())
        emb[v] = np.stack(out)
        truncados[v] = tr
        np.save(os.path.join(a.salida, f"emb_{v}.npy"), emb[v])
        print(v, emb[v].shape, f"{time.time() - t0:.0f} s", flush=True)
    assert all(np.isfinite(e).all() for e in emb.values())
    pts = {}
    for v in emb:
        X = emb[v][:, None, :].astype(np.float32)  # una sola «capa»
        res = ref.correr_condicion(X, y, g, ref.SEMILLAS, 2)
        pts[v], _ = ref.puntajes(res, len(y))
    b = ref.bootstrap(y, g, [pts["completo"], pts["solo_lean"]])
    R = {"modelo": MODELO, "revision": REVISION, "n": int(len(y)), "truncados": truncados,
         "auroc_completo": b[0][0], "ic_completo": list(b[0][1:]),
         "auroc_solo_lean": b[1][0], "ic_solo_lean": list(b[1][1:]),
         "delta": b[2][0], "ic_delta": list(b[2][1:]), "segundos": round(time.time() - t0)}
    json.dump(R, open(os.path.join(AQUI, "v2_control_embeddings_bge_m3.json"), "w"), indent=1, default=float)
    print(json.dumps(R, indent=1, default=float))


if __name__ == "__main__":
    main()
