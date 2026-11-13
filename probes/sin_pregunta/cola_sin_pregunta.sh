#!/bin/zsh
# Extracción sin la pregunta (11 nov 2026): completo y solo_lean, Niveles A y B, un modelo a la vez.
# No ajusta sondas ni lee etiquetas. Reanudable: si se corta, se vuelve a lanzar igual.
# Uso:  zsh probes/sin_pregunta/cola_sin_pregunta.sh                 (los cuatro modelos del Nivel B)
#       zsh probes/sin_pregunta/cola_sin_pregunta.sh qwen3_4b        (solo ese)
cd "/Users/cmorregof/Personal/Proyecto Godel" || exit 1
PY=biblioteca/.venv/bin/python; S=probes/sin_pregunta; OUT=probes/activaciones/sin_pregunta
if (( $# )); then MODELOS=("$@"); else MODELOS=(qwen3_4b gemma3_4b llama31_8b olmo2_7b); fi
pgrep -f "probes/extraer.py|extraer_pares.py --candidatos.*--salida|extraer_sin_pregunta.py" >/dev/null && { echo "Ya hay una extracción en GPU. Un modelo a la vez."; exit 2; }
mkdir -p $OUT
nota() { echo "- [$(date '+%Y-%m-%d %H:%M %Z')] cola_sin_pregunta.sh: $1" >> probes/BITACORA.md; }
for n in $MODELOS; do
  for niv in a b; do
    pre=""; [[ $niv == b ]] && pre="nivel_b_"
    nota "inicio $n, nivel $niv (completo y solo_lean sin la pregunta)"
    HF_HUB_OFFLINE=1 caffeinate -i $PY -I $S/extraer_sin_pregunta.py --nivel $niv --nombre $n --bitacora >> $OUT/${pre}${n}.log 2>&1
    nota "$n, nivel $niv: terminó con código $?"
  done
done
echo "Listo. Comparaciones en $OUT/*/comprobacion_causal.json y al final de cada log."
