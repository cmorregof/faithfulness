#!/bin/zsh
# Cola del Nivel C: por modelo, las diez corridas de elegir_capa_anidada en procesos separados, luego cierre y barajadas.
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
PY=../../biblioteca/.venv/bin/python
echo "inicio cola C $(date '+%Y-%m-%d %H:%M:%S %z')"
for par in "qwen3_4b_proofnetverif 5" "llama31_8b_proofnetverif 5"; do
  m=${par% *}; n=${par#* }
  $PY correr_nivel_c.py $m datos > nivel_c_${m}_datos.log 2>&1 || { echo "$m datos fallo"; continue; }
  for v in completo solo_lean; do for s in 0 1 2 3 4; do echo "$v $s"; done; done | \
    xargs -P $n -L 1 zsh -c "$PY correr_nivel_c.py $m i \$0 \$1 >> nivel_c_${m}_i_\$0_s\$1.log 2>&1; echo \"$m \$0 s\$1 codigo \$? \$(date '+%H:%M:%S')\""
  $PY correr_nivel_c.py $m i_cierre > nivel_c_${m}_cierre.log 2>&1; echo "$m cierre codigo $? $(date '+%H:%M:%S')"
  $PY correr_nivel_c.py $m barajadas > nivel_c_${m}_barajadas.log 2>&1; echo "$m barajadas codigo $? $(date '+%H:%M:%S')"
done
echo "fin cola C $(date '+%Y-%m-%d %H:%M:%S %z')"
