#!/bin/zsh
# Nivel B: extracción de activaciones de los pares certificados con Qwen3-4B (GPU). PREPARADO; NO LANZADO.
# Extrae las 1086 filas del parquet (270 originales + 408 infieles + 408 fieles, 4 variantes, 4344 pases);
# las exclusiones de datos/exclusiones_nivel_b.json se aplican en el ANÁLISIS (principal 377 pares; los
# 23 «equivalentes de hecho» se reportan aparte), no aquí. Reanudable (extraer.py).
# Probado de punta a punta con --limite 5 el 5 nov 2026 (scratchpad; finitos, sin truncados, masa P(Yes) = 1).
# Se niega a correr sin las firmas de Carlos (decisión del 5 nov: no se extrae hasta que firme la regla de
# tripletas y la muestra de 30) y si el parquet no es el fijado en exclusiones_nivel_b.json.
cd "/Users/cmorregof/Personal/Proyecto Godel" || exit 1
NB=probes/nivel_b; PY=biblioteca/.venv/bin/python
for m in APROBADO_regla_tripletas APROBADO_muestra_tripletas; do
  [[ -f $NB/$m ]] || { echo "Falta $NB/$m (la crea solo Carlos). Me niego."; exit 2; }
done
SHA=$(shasum -a 256 $NB/datos/pares_nivel_b.parquet | cut -c1-64)
ESP=$($PY -I -c "import json;print(json.load(open('$NB/datos/exclusiones_nivel_b.json'))['sha256_parquet'])")
[[ $SHA == $ESP ]] || { echo "El parquet ($SHA) no es el fijado en las exclusiones ($ESP). Me niego."; exit 2; }
pgrep -f "probes/extraer.py|extraer_pares.py --candidatos.*--salida" >/dev/null && { echo "Ya hay una extracción en GPU. Un modelo a la vez."; exit 2; }
echo "- [$(date '+%Y-%m-%d %H:%M %Z')] extraer_nivel_b.sh: inicio (Qwen3-4B, 1086 filas, 4 variantes); memoria: $(memory_pressure | tail -1)" >> probes/BITACORA.md
HF_HUB_OFFLINE=1 caffeinate -i $PY -I $NB/extraer_pares.py --candidatos $NB/candidatos_v3.jsonl --dir_parquet $NB/datos \
  --salida probes/activaciones/nivel_b_qwen3_4b --modelo Qwen/Qwen3-4B --revision 1cfa9a7208912126459214e8b04321603b3df60c \
  --bitacora --cada 200 >> probes/activaciones/nivel_b_qwen3_4b.log 2>&1
echo "- [$(date '+%Y-%m-%d %H:%M %Z')] extraer_nivel_b.sh: terminó con código $?" >> probes/BITACORA.md
