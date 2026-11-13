#!/bin/zsh
# Nivel B (5 nov, aprobado por Carlos 22:44): tras la extracción, análisis pareado (desarrollo/exploratorio)
# principal (377) y sensibilidades (408; sin 4/45/56/203). --jobs 2.
cd "/Users/cmorregof/Personal/Proyecto Godel" || exit 1
PY=biblioteca/.venv/bin/python; NB=probes/nivel_b; A=probes/activaciones/nivel_b_qwen3_4b
nota() { echo "- [$(date '+%Y-%m-%d %H:%M %Z')] analizar_nivel_b_cola.sh: $1" >> probes/BITACORA.md; }
while pgrep -f "extraer_pares.py --candidatos" >/dev/null; do sleep 60; done
ok=$($PY -I -c "import json;m=json.load(open('$A/meta.json'));print(len(m.get('variantes_completas',[])))")
[[ $ok == 4 ]] || { nota "extracción incompleta (variantes completas: $ok); no analizo"; exit 1; }
nota "extracción completa (4 variantes); inicio del análisis principal (377 pares, --jobs 7)"
for n in principal:pares_indice_principal sens_408:pares_indice_completo_vv sens_sin_dudosos:pares_indice_sens_sin_dudosos; do
  nom=${n%%:*}; ind=${n#*:}
  nice $PY -I $NB/analizar_pares.py --carpeta $A --indice $NB/datos/$ind.jsonl --nombre qwen3_4b_$nom --salida $NB/resultados --jobs 7 > $NB/resultados_$nom.log 2>&1
  nota "análisis $nom terminó (código $?); log $NB/resultados_$nom.log"
done
