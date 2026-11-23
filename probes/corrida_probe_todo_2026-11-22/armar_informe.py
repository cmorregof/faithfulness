"""Arma probes/resultados_probe_todo_2026-11-22.md: prosa de informe_plantilla.md más las tablas de tablas_informe.py.

Cada marcador {{nombre}} de la plantilla se sustituye por la tabla correspondiente. No calcula nada.
"""
import contextlib, io, re
from pathlib import Path
import tablas_informe as T

AQUI = Path(__file__).resolve().parent


def cap(f, *a):
    b = io.StringIO()
    with contextlib.redirect_stdout(b):
        f(*a)
    return b.getvalue().rstrip("\n")


FRAG = {
    "A_principal": cap(T.tabla_principal, "nivel_a", T.NIVEL_A, ("i", "ii")),
    "A_capas": cap(T.tabla_capas, "nivel_a", T.NIVEL_A),
    "A_capas_elegidas": cap(T.tabla_capas_elegidas, "nivel_a", T.NIVEL_A),
    "A_correlacion": cap(T.tabla_correlacion, "nivel_a", T.NIVEL_A, ("i", "ii")),
    "A_barajadas": cap(T.tabla_barajadas, "nivel_a", T.NIVEL_A),
    "A_tiempos": cap(T.tabla_tiempos, "nivel_a", T.NIVEL_A, ("i", "ii")),
    "C_principal": cap(T.tabla_principal, "nivel_c", T.NIVEL_C, ("i",)),
    "C_capas": cap(T.tabla_capas, "nivel_c", T.NIVEL_C),
    "C_capas_elegidas": cap(T.tabla_capas_elegidas, "nivel_c", T.NIVEL_C),
    "C_correlacion": cap(T.tabla_correlacion, "nivel_c", T.NIVEL_C, ("i",)),
    "C_barajadas": cap(T.tabla_barajadas, "nivel_c", T.NIVEL_C),
    "C_tiempos": cap(T.tabla_tiempos, "nivel_c", T.NIVEL_C, ("i",)),
}
texto = (AQUI / "informe_plantilla.md").read_text(encoding="utf-8")
usados = set(re.findall(r"\{\{(\w+)\}\}", texto))
assert usados <= set(FRAG), usados - set(FRAG)
for k in usados:
    texto = texto.replace("{{" + k + "}}", FRAG[k])
assert "| sin comparar |" not in texto, "queda algún modelo sin comparar"
(AQUI.parent / "resultados_probe_todo_2026-11-22.md").write_text(texto, encoding="utf-8")
print("escrito", AQUI.parent / "resultados_probe_todo_2026-11-22.md", len(texto), "caracteres; marcadores:", sorted(usados))
