import json, sys, time
from pathlib import Path
import numpy as np
import pyarrow.parquet as pq
R = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(R))
C = R / "activaciones" / "qwen3_4b"
for v in ("completo", "solo_lean"):
    for p in ("ultimo", "media_lean"):
        a = np.load(C / f"acts_{v}_{p}.npy", mmap_mode="r")
        print(v, p, a.shape, a.dtype)
for v in ("completo", "solo_lean"):
    a = np.load(C / f"pyes_{v}.npy"); print("pyes", v, a.shape, a.dtype)
man = [json.loads(l) for l in open(C / "manifiesto.jsonl", encoding="utf-8") if l.strip()]
print("claves manifiesto:", list(man[0]))
print("idx en orden:", [m["idx"] for m in man] == list(range(500)))
y = np.array([m["etiqueta"] for m in man]); comp = np.array([m["compila"] for m in man])
print("N", len(y), "pos", int(y.sum()), "compila", int(comp.sum()), "pos|compila", int(y[comp==1].sum()), "neg|compila", int((1-y[comp==1]).sum()))
print("grupos unicos:", len({m["grupo"] for m in man}), "entre los 450:", len({m["grupo"] for m in man if m["compila"]}))
t = pq.read_table(R / "datos" / "criticleanbench_test.parquet")
print("columnas parquet:", t.column_names, "filas:", t.num_rows)
d = t.to_pydict()
for k in set(man[0]) & set(d):
    print("  comun", k, "coinciden en orden:", sum(d[k][i] == man[i][k] for i in range(500)), "/ 500; unicos:", len(set(d[k])))
