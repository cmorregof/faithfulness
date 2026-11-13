#!/bin/bash
# Nivel B: certificación -> parquet de pares -> COMPUERTA DE SUPERFICIE -> extracción de activaciones
# -> análisis pareado. PREPARADO; NO LANZADO. Reanudable: cada paso deja una marca HECHO_* y se salta
# si ya está.
#
# Lote: candidatos_v3.jsonl (revisor Fable, 2026-11-04; candidatos.jsonl v1 queda como histórico).
#
# Se niega a correr sin las marcas que SOLO crea Carlos en probes/nivel_b/:
#   APROBADO_reglas          reglas del generador aprobadas; su contenido debe incluir el SHA-256
#                            actual de candidatos_v3.jsonl (el que quedó registrado en
#                            prometeo_lean/aprobados/ con su línea en FECHA)
#   APROBADO_muestra         revisó muestra_30_v3.md
#   APROBADO_regla_decision  regla de decisión del Nivel B aprobada (regla_borrador.md, ya definitiva)
#   APROBADO_lean            su bucle de Lean terminó: se puede usar Lean en esta máquina
#
# Uso:  bash probes/nivel_b/lanzar.sh            (variables: PROCESOS=4 MODELO=Qwen/Qwen3-4B
#                                                  REVISION=1cfa9a72... NOMBRE=qwen3_4b JOBS=5
#                                                  CRITERIO=estricto|firma  para la compuerta)
set -euo pipefail

RAIZ="$(cd "$(dirname "$0")/../.." && pwd)"
NB="$RAIZ/probes/nivel_b"
PY="$RAIZ/biblioteca/.venv/bin/python"
BIT="$RAIZ/probes/BITACORA.md"
PROCESOS="${PROCESOS:-4}"
MODELO="${MODELO:-Qwen/Qwen3-4B}"
REVISION="${REVISION:-1cfa9a7208912126459214e8b04321603b3df60c}"
NOMBRE="${NOMBRE:-qwen3_4b}"
JOBS="${JOBS:-5}"
CRITERIO="${CRITERIO:-firma}"  # decisión de Carlos del 4 nov, 17:58 (bitácora); antes «estricto»
CAND="$NB/candidatos_v3.jsonl"
ACTS="$RAIZ/probes/activaciones/nivel_b_$NOMBRE"

nota() { echo "$1"; echo "- [$(date '+%Y-%m-%d %H:%M %Z')] lanzar.sh (nivel B): $1" >> "$BIT"; }

# ---- 0. compuertas
falta=0
for m in APROBADO_reglas APROBADO_muestra APROBADO_regla_decision APROBADO_lean; do
  if [ ! -f "$NB/$m" ]; then echo "Falta la marca $NB/$m (la crea Carlos)."; falta=1; fi
done
if [ "$falta" = 1 ]; then echo "Me niego a correr sin las cuatro marcas de aprobación."; exit 2; fi
if [ ! -f "$CAND" ]; then echo "Falta $CAND (generar.py --v3)."; exit 2; fi
SHA="$(shasum -a 256 "$CAND" | cut -d' ' -f1)"
if ! grep -q "$SHA" "$NB/APROBADO_reglas"; then
  echo "APROBADO_reglas no contiene el SHA-256 actual de candidatos_v3.jsonl ($SHA). Me niego."; exit 2
fi
nota "inicio; candidatos_v3.jsonl $SHA; $PROCESOS procesos de Lean; modelo $MODELO@${REVISION:0:8}; compuerta $CRITERIO"

# ---- 1. certificación (Lean, CPU)
if [ ! -f "$NB/certificacion/HECHO_certificacion" ]; then
  nota "1/5 certificación: inicio"
  "$PY" -I "$NB/certificar.py" --candidatos "$CAND" --procesos "$PROCESOS" --salida "$NB/certificacion" --bitacora
  touch "$NB/certificacion/HECHO_certificacion"
  nota "1/5 certificación: fin ($(cat "$NB/certificacion/resumen.json" | "$PY" -c 'import json,sys; print(json.load(sys.stdin)["por_estado"])'))"
fi

# ---- 2. parquet de pares certificados
if [ ! -f "$NB/datos/HECHO_parquet" ]; then
  mkdir -p "$NB/datos"
  "$PY" -I "$NB/extraer_pares.py" --candidatos "$CAND" --solo_parquet --dir_parquet "$NB/datos" | tee "$NB/datos/parquet.json"
  touch "$NB/datos/HECHO_parquet"
  nota "2/5 parquet: $(cat "$NB/datos/parquet.json")"
fi
PARES="$("$PY" -c 'import json,sys; print(json.load(open(sys.argv[1]))["pares"])' "$NB/datos/parquet.json")"
if [ "$PARES" -lt 200 ]; then
  nota "solo $PARES pares certificados (< 200, umbral mínimo de la regla): me detengo antes de extraer."
  exit 3
fi

# ---- 3. compuerta de superficie sobre los pares certificados (CPU, sin modelo)
if [ ! -f "$NB/datos/HECHO_compuerta" ]; then
  if "$PY" -I "$NB/compuerta_superficie.py" --candidatos "$CAND" --indice "$NB/datos/pares_indice.jsonl" \
        --criterio "$CRITERIO" --salida "$NB/datos/compuerta_superficie_certificados.json"; then
    touch "$NB/datos/HECHO_compuerta"
    nota "3/5 compuerta de superficie ($CRITERIO): pasa; $(cat "$NB/datos/compuerta_superficie_certificados.json" | "$PY" -c 'import json,sys; R=json.load(sys.stdin); print({k: round(R[k],3) for k in ("auroc_pareada_solo_lean","auroc_pareada_tipicidad_no_supervisada","exceso_firma")})')"
  else
    nota "3/5 compuerta de superficie ($CRITERIO): NO PASA; me detengo antes de extraer. Ver probes/nivel_b/datos/compuerta_superficie_certificados.json"
    exit 4
  fi
fi

# ---- 4. extracción de activaciones (GPU), reanudable como extraer.py
if [ ! -f "$ACTS/HECHO_extraccion" ]; then
  nota "4/5 extracción: inicio ($PARES pares) en $ACTS"
  HF_HUB_OFFLINE=1 "$PY" -I "$NB/extraer_pares.py" --candidatos "$CAND" --dir_parquet "$NB/datos" \
      --salida "$ACTS" --modelo "$MODELO" --revision "$REVISION" --bitacora --cada 200
  touch "$ACTS/HECHO_extraccion"
  nota "4/5 extracción: fin"
fi

# ---- 5. análisis pareado (CPU)
if [ ! -f "$NB/resultados/HECHO_$NOMBRE" ]; then
  nota "5/5 análisis pareado: inicio"
  "$PY" -I "$NB/analizar_pares.py" --carpeta "$ACTS" --indice "$NB/datos/pares_indice.jsonl" \
      --nombre "$NOMBRE" --salida "$NB/resultados" --jobs "$JOBS"
  mkdir -p "$NB/resultados"; touch "$NB/resultados/HECHO_$NOMBRE"
  nota "5/5 análisis pareado: fin; informe probes/nivel_b/resultados/nivel_b_$NOMBRE.md"
fi
