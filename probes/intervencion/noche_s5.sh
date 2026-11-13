#!/bin/zsh
# Noche del 11 al 12 de noviembre de 2026. Una sola corrida de GPU a la vez.
#   1. S5 en Qwen3-4B: direcciones, humo (comprueba los ganchos), corrida completa y análisis.
#      Si falta la marca de aprobación o falla un paso, S5 se salta y la noche sigue.
#   2. Extracción sin pregunta de Gemma-3, Llama-3.1 y OLMo-2 (S1 en los otros tres modelos).
#   3. S2 (CPU) para esos tres, solo si S2 ya terminó bien en Qwen3-4B.
# Uso, desde cualquier carpeta:   caffeinate -i zsh probes/intervencion/noche_s5.sh
# Todo queda en probes/intervencion/noche_s5.log. No reanuda los entrenamientos en pausa.

cd "$(dirname "$0")/../.." || exit 1
PY=biblioteca/.venv/bin/python
[ -x "$PY" ] || { echo "No encuentro $PY (hay que lanzarlo dentro de Proyecto Godel)."; exit 1; }
export HF_HUB_OFFLINE=1
S5=probes/intervencion/intercambio.py
S2=probes/sin_pregunta/analisis_s2_s3.py
RES=probes/sin_pregunta/resultados
LOG=probes/intervencion/noche_s5.log
OTROS=(gemma3_4b llama31_8b olmo2_7b)

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

s5() {
  if [ ! -f probes/intervencion/APROBADO_regla_S5 ]; then
    echo "Falta probes/intervencion/APROBADO_regla_S5: S5 no corre esta noche."
    return 1
  fi
  paso "S5 direcciones (CPU)" "$PY" -I "$S5" --paso direcciones || return 1
  paso "S5 humo: 4 pares, 9 condiciones" "$PY" -I "$S5" --paso correr --prueba 4 || return 1
  paso "S5 corrida completa: 754 filas, 54 condiciones" "$PY" -I "$S5" --paso correr || return 1
  paso "S5 análisis" "$PY" -I "$S5" --paso analizar || return 1
}

{
  echo ""
  echo "################ noche S5, $(date '+%Y-%m-%d %H:%M') ################"
  s5 && S5_OK=sí || S5_OK=no

  paso "cola sin pregunta: ${OTROS[*]}" zsh probes/sin_pregunta/cola_sin_pregunta.sh "${OTROS[@]}"

  if [ -f "$RES/s2a_qwen3_4b.json" ] && [ -f "$RES/s2b_qwen3_4b.json" ]; then
    for m in "${OTROS[@]}"; do
      if [ -d "probes/activaciones/sin_pregunta/nivel_b_$m" ]; then
        paso "S2b $m (CPU)" "$PY" -I "$S2" --paso s2b --nombre "$m"
      else
        echo "Sin extracción sin pregunta del Nivel B de $m: no corro su S2b."
      fi
      if [ -d "probes/activaciones/sin_pregunta/$m" ]; then
        paso "S2a $m (CPU)" "$PY" -I "$S2" --paso s2a --nombre "$m"
      else
        echo "Sin extracción sin pregunta del Nivel A de $m: no corro su S2a."
      fi
    done
  else
    echo ""
    echo "S2 de Qwen3-4B no ha dejado sus dos resultados: no encadeno S2 en los otros modelos."
  fi

  echo ""
  echo "################ fin, $(date '+%Y-%m-%d %H:%M') ################"
  echo "S5 completo: $S5_OK"
  [ -f probes/intervencion/resultados_s5/qwen3_4b/s5.json ] && echo "  resultado: probes/intervencion/resultados_s5/qwen3_4b/s5.json"
  for m in "${OTROS[@]}"; do
    for d in "$m" "nivel_b_$m"; do
      [ -d "probes/activaciones/sin_pregunta/$d" ] && echo "  sin pregunta $d: hay carpeta" || echo "  sin pregunta $d: FALTA"
    done
  done
  for f in "$RES"/s2?_*.json(N); do echo "  $f"; done
  echo "Los dos entrenamientos siguen en pausa (kill -CONT 29700 59556 para reanudarlos)."
} 2>&1 | tee -a "$LOG"
