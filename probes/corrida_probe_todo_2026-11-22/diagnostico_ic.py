"""Diagnóstico desde fuera: ¿la diferencia en el intervalo de Δ viene de los puntajes o del bootstrap?

Aplica probe.diferencia_pareada (sin cambios, semilla 0, 2000 remuestreos) a los puntajes que la
referencia guardó en sus .npz, y lo pone junto al intervalo que la referencia reporta y al de probe.py.
No lee código de la referencia. Solo se corre para modelos que ya tienen comparacion.json.
"""
import json, sys
from pathlib import Path
import numpy as np
AQUI = Path(__file__).resolve().parent
R = AQUI.parent
sys.path.insert(0, str(R))
import probe
LECT = {"i": "i_ultimo_cv", "ii": "ii_media_lean_capa_fija"}
res = {}
for modelo in sys.argv[1:]:
    S = AQUI / "salida" / "nivel_a" / modelo
    assert (S / "comparacion.json").exists(), modelo
    ref = json.loads((R / "referencia" / f"v2_resultados_{modelo}.json").read_text(encoding="utf-8"))
    res[modelo] = {}
    for corta, larga in LECT.items():
        zp = np.load(S / f"puntajes_{corta}.npz"); zr = np.load(R / "referencia" / f"v2_puntajes_{modelo}_{larga}.npz")
        assert np.array_equal(zp["y"], zr["y"])
        y, g = zp["y"], zp["grupos"]
        a = probe.diferencia_pareada(y, zr["completo"], zr["solo_lean"], g, semilla=probe.SEMILLA)
        mio = json.loads((S / f"lectura_{corta}.json").read_text(encoding="utf-8"))["delta"]
        r = ref["lecturas"][larga]
        res[modelo][corta] = {"probe_py": mio, "referencia_reportado": [r["delta"], *r["ic_delta"]],
                              "puntajes_de_referencia_con_bootstrap_de_probe_py": list(a)}
        print(f"{modelo:13s} ({corta})  probe.py {mio[0]:+.4f} [{mio[1]:+.4f}, {mio[2]:+.4f}] | referencia {r['delta']:+.4f} [{r['ic_delta'][0]:+.4f}, {r['ic_delta'][1]:+.4f}]"
              f" | puntajes de la referencia con el bootstrap de probe.py {a[0]:+.4f} [{a[1]:+.4f}, {a[2]:+.4f}]")
(AQUI / "salida" / "nivel_a" / "diagnostico_ic.json").write_text(json.dumps(res, ensure_ascii=False, indent=2), encoding="utf-8")
