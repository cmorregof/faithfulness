#!/bin/zsh
# Nivel C (ProofNetVerif): extracción de activaciones y probes de referencia.
#
#   (i)  --solo_extraccion   Qwen3-4B, cuatro variantes (completo, solo_lean, solo_nl,
#                            nl_desemparejado), 3752 filas = 15 008 pases. Reanudable: si se corta,
#                            se relanza igual y sigue donde quedó. Avance en probes/BITACORA.md.
#                            Esta parte NO necesita aprobación (solo produce activaciones).
#   (ii) --probes            probes/nivel_c/probe_c.py. SE NIEGA A CORRER si no existe
#                            probes/nivel_c/APROBADO_regla_decision (la crea solo Carlos tras
#                            aprobar probes/nivel_c/regla_borrador.md).
#        --todo              (i) y luego (ii) (ii sigue negándose sin la marca).
#        --verificar         comprobación sin modelo: parquet, desarreglo, prompts con el
#                            tokenizador, estimación de tiempo. No usa la GPU.
#   PRUEBA=1                 con --solo_extraccion: solo 5 filas, carpeta *_prueba5.
#
# Uso (desde cualquier carpeta):
#   zsh probes/nivel_c/lanzar.sh --solo_extraccion
# Estimado de (i): 15 008 pases × 0,42–0,75 s ≈ 1,7–3,1 h (Qwen3-4B en MPS; ver
# probes/nivel_c/verificacion_extraccion.json). Pico de memoria esperado ≈ el de CriticLeanBench
# (8,8 GiB) o menos: los prompts son más cortos (mediana 154 tokens en «completo»).

cd "$(dirname "$0")/../.." || exit 1
PY=biblioteca/.venv/bin/python
C=probes/nivel_c
DATOS=$C/datos_proc/proofnetverif.parquet
SHA_DATOS=2b912a38c4ba63690d60d8a1c084b828b49b8ab02db6e348cc98b7677861d695
SALIDA=$C/activaciones/qwen3_4b_proofnetverif
LOG=$C/extraccion_qwen3_4b_proofnetverif.log
MODELO=Qwen/Qwen3-4B
REV=1cfa9a7208912126459214e8b04321603b3df60c
export HF_HUB_OFFLINE=1

nota() { echo "- [$(date '+%Y-%m-%d %H:%M %Z')] nivel_c/lanzar.sh: $1" >> probes/BITACORA.md; }

comprobar_datos() {
  if [[ ! -f $DATOS ]]; then
    "$PY" -I $C/preparar_proofnetverif.py > /dev/null || { echo "falló preparar_proofnetverif.py"; return 1; }
  fi
  local h=$(shasum -a 256 "$DATOS" | cut -d' ' -f1)
  if [[ $h != $SHA_DATOS ]]; then
    echo "SHA-256 de $DATOS distinto ($h); no sigo."; nota "SHA-256 del parquet distinto; no se extrajo"; return 1
  fi
}

extraccion() {
  comprobar_datos || return 1
  local extra=() suf=""
  if [[ -n "$PRUEBA" ]]; then extra=(--limite 5) suf="_prueba5"; fi
  mkdir -p "$(dirname $SALIDA)"
  echo "=== $(date) ===" >> "$LOG"
  caffeinate -i "$PY" -I $C/extraer_c.py --modelo $MODELO --revision $REV \
    --datos "$DATOS" --nombre_datos "PAug/ProofNetVerif@91183e5b12d64374827bf2782db629b5b0f8f319 (valid+test)" \
    --salida "$SALIDA$suf" --bitacora --cada 500 "${extra[@]}" >> "$LOG" 2>&1
  local rc=$?
  if [[ $rc -ne 0 ]]; then nota "extracción terminó con error (código $rc); ver $LOG"; fi
  return $rc
}

probes() {
  if [[ ! -f $C/APROBADO_regla_decision ]]; then
    echo "Me niego a correr los probes: falta $C/APROBADO_regla_decision (la crea solo Carlos)."
    return 2
  fi
  "$PY" -I $C/probe_c.py --carpeta "$SALIDA" --carpeta_cl probes/activaciones/qwen3_4b \
    --nombre qwen3_4b --jobs 6 >> $C/probes_qwen3_4b_proofnetverif.log 2>&1
  local rc=$?
  nota "probe_c.py terminó (código $rc); log $C/probes_qwen3_4b_proofnetverif.log"
  return $rc
}

case "$1" in
  --solo_extraccion) extraccion ;;
  --probes)          probes ;;
  --todo)            extraccion && probes ;;
  --verificar)       comprobar_datos && "$PY" -I $C/verificar_extraccion.py --datos "$DATOS" ;;
  *) sed -n '2,21p' "$0"; exit 1 ;;
esac
