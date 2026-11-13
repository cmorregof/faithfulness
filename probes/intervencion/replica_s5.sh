#!/bin/zsh
# Réplica de S5 en Gemma-3, OLMo-2 y Llama-3.1. Una sola corrida de GPU a la vez, un modelo tras otro.
# Por modelo: direcciones, humo (ganchos + que el prompt reproduzca la extracción guardada), corrida completa
# y análisis. Si un paso falla, ese modelo se deja y sigue el siguiente. Un modelo con s5.json ya hecho se salta.
# Se puede cortar con Ctrl-C y volver a lanzar: la corrida completa reanuda donde iba.
# Uso, desde cualquier carpeta:   caffeinate -i zsh probes/intervencion/replica_s5.sh [modelos...]
# Todo queda en probes/intervencion/replica_s5.log. No reanuda los entrenamientos en pausa.

cd "$(dirname "$0")/../.." || exit 1
PY=biblioteca/.venv/bin/python
[ -x "$PY" ] || { echo "No encuentro $PY (hay que lanzarlo dentro de Proyecto Godel)."; exit 1; }
export HF_HUB_OFFLINE=1
R=probes/intervencion/replica_s5.py
RES=probes/intervencion/resultados_s5
LOG=probes/intervencion/replica_s5.log
MODELOS=(gemma3_4b olmo2_7b llama31_8b)
[ $# -gt 0 ] && MODELOS=("$@")

hora() { date '+%H:%M'; }

paso() {   # paso "nombre" orden...   → corre, anota la hora y devuelve el código de salida
  local nombre="$1"; shift
  echo ""
  echo "=== [$(hora)] $nombre"
  "$@"
  local rc=$?
  if [ $rc -eq 0 ]; then echo "=== [$(hora)] $nombre: hecho"; else echo "=== [$(hora)] $nombre: FALLÓ (código $rc)"; fi
  return $rc
}

uno() {
  local m="$1"
  if [ -f "$RES/$m/s5.json" ]; then echo ""; echo "=== $m ya tiene s5.json: lo salto."; return 0; fi
  paso "$m: direcciones (CPU)" "$PY" -I "$R" --paso direcciones --nombre "$m" || return 1
  paso "$m: humo, 4 pares y 9 condiciones" "$PY" -I "$R" --paso humo --nombre "$m" || return 1
  paso "$m: corrida completa, 754 filas y 54 condiciones" "$PY" -I "$R" --paso correr --nombre "$m" || return 1
  paso "$m: análisis" "$PY" -I "$R" --paso analizar --nombre "$m" || return 1
}

{
  echo ""
  echo "################ réplica de S5, $(date '+%Y-%m-%d %H:%M') ################"
  if [ ! -f probes/intervencion/APROBADO_regla_S5_replica ]; then
    echo "Falta probes/intervencion/APROBADO_regla_S5_replica: no corre nada."
  else
    for m in "${MODELOS[@]}"; do
      uno "$m" || echo "=== $m queda sin terminar; sigo con el siguiente."
    done
    paso "resumen de la réplica" "$PY" -I "$R" --paso resumen
  fi
  echo ""
  echo "################ fin, $(date '+%Y-%m-%d %H:%M') ################"
  echo "Los dos entrenamientos siguen en pausa (kill -CONT 29700 59556 para reanudarlos)."
} 2>&1 | tee -a "$LOG"
