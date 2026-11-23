"""Comprueba forma, dtype y conteos del manifiesto de cada carpeta de activaciones del Nivel A."""
import json, sys
from pathlib import Path
import numpy as np
R = Path(__file__).resolve().parent.parent
for m in sys.argv[1:]:
    C = R / "activaciones" / m
    formas = {}
    for v in ("completo", "solo_lean"):
        for p in ("ultimo", "media_lean"):
            a = np.load(C / f"acts_{v}_{p}.npy", mmap_mode="r")
            formas[f"{v}_{p}"] = (a.shape, str(a.dtype))
    man = [json.loads(l) for l in open(C / "manifiesto.jsonl", encoding="utf-8") if l.strip()]
    y = np.array([x["etiqueta"] for x in man]); comp = np.array([x["compila"] for x in man])
    meta = json.loads((C / "meta.json").read_text(encoding="utf-8")) if (C / "meta.json").exists() else {}
    iguales = len(set(formas.values())) == 1
    print(m, "| formas iguales:", iguales, list(formas.values())[0] if iguales else formas,
          "| idx en orden:", [x["idx"] for x in man] == list(range(len(man))),
          "| N", len(y), "compila", int(comp.sum()), "pos|compila", int(y[comp == 1].sum()), "neg|compila", int((1 - y[comp == 1]).sum()),
          "| grupos entre los que compilan:", len({x["grupo"] for x in man if x["compila"]}))
    print("   meta:", {k: meta[k] for k in meta if k in ("modelo", "modelo_id", "revision", "n_capas", "num_capas", "dtype", "dispositivo", "capas", "dim")} or list(meta)[:20])
