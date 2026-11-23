#!/bin/zsh
# Cola del Nivel A: siete modelos, hasta cuatro a la vez, un hilo por proceso; después main() de Qwen3-4B.
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1
PY=../../biblioteca/.venv/bin/python
echo "inicio cola $(date '+%Y-%m-%d %H:%M:%S %z')"
printf '%s\n' olmo2_7b gemma3_4b llama31_8b dsprover2_7b goedel_8b kimina_7b qwen3_8b | \
  xargs -P 4 -I{} zsh -c "s=\$(date +%s); $PY correr_nivel_a.py {} > nivel_a_{}.log 2>&1; echo \"{} codigo \$? \$(( \$(date +%s) - s )) s\""
echo "fin nivel A $(date '+%Y-%m-%d %H:%M:%S %z')"
$PY correr_main.py > main_qwen3_4b.log 2>&1; echo "main codigo $?"
echo "fin cola $(date '+%Y-%m-%d %H:%M:%S %z')"
