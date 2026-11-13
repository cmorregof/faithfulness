# Prerregistro v2: piloto de adecuación NL ↔ Lean (Nivel A, réplicas)

**Firmado por Carlos Orrego-Franco el 4 nov 2026 a las 22:29 (Bogotá).** Redactado por el orquestador (Claude Code) a partir del prompt de Carlos de esa noche. El SHA-256 de este archivo queda en `probes/BITACORA.md` y la copia en `probes/prerregistros/`. Sustituye, para todo lo que se corra desde ahora, a la regla de decisión de las 12:55 y sus precisiones de las 13:37. Esa regla sigue valiendo para lo ya corrido.

El documento tiene dos partes. Las secciones 1 a 8 son el contenido que Carlos firmó. La sección 9 recoge las precisiones del orquestador, es decir, lo que el texto firmado no fijaba y hace falta para poder correrlo. Esas precisiones están **pendientes de confirmación de Carlos**: si él cambia alguna, se anota como desviación con su hora.

## 1. Estado de lo ya visto
- **Qwen3-4B** pasa a ser **exploratorio**. Su resultado bajo la regla de las 12:55 (completo − solo Lean = +0,088 [+0,039; +0,134]) se vio antes de este prerregistro y no cuenta como confirmación.
- **Goedel-Prover-V2-8B** y **Kimina-Autoformalizer-7B** se reportan como **réplicas fallidas bajo el criterio nuevo**, sin reinterpretarlas. Bajo la regla vieja sus IC excluían el 0, pero el p de la permutación de la diferencia fue 0,16 y 0,25. Se recalculan con el procedimiento de este prerregistro con el rótulo «exploratorio / réplica fallida, recalculado».

## 2. Modelos nuevos (fijos, en este orden)
1. `allenai/OLMo-2-1124-7B-Instruct`
2. `google/gemma-3-4b-it`, cargado como modelo causal de texto
3. `meta-llama/Llama-3.1-8B-Instruct`
4. `deepseek-ai/DeepSeek-Prover-V2-7B`

`Qwen/Qwen3-8B` (base) es **solo exploratorio**. La revisión exacta (commit de Hugging Face), la licencia y los hashes de cada modelo se anotan en la bitácora al descargarlo, antes de extraer.

## 3. Datos, plantilla y particiones
- **Datos:** CriticLeanBench (`m-a-p/CriticLeanBench@6225522b`, parquet SHA-256 `baf3e43b…`), las **450 filas que compilan** (250 adecuadas y 200 inadecuadas). Las etiquetas son humanas, de CriticLeanBench, no decididas por Lean.
- **Plantilla:** la misma plantilla de usuario del Nivel A (`probes/extraer.py`: `PLANTILLA_COMPLETO`, `PLANTILLA_SOLO_LEAN`, `PLANTILLA_SOLO_NL`), con `tokenizer.apply_chat_template([{"role": "user", …}], add_generation_prompt=True)`.
- **Variantes:** completo, solo_lean, solo_nl y nl_desemparejado, con el mismo desarreglo (semilla 0, quintiles de longitud del NL, nunca el mismo grupo).
- **Particiones y grupos:** los mismos que en el Nivel A, es decir, StratifiedGroupKFold(5) por enunciado NL normalizado, con semillas 0–4.

## 4. Primario por modelo
La medida primaria es la diferencia **Δ = AUROC(completo) − AUROC(solo Lean)**. Se evalúan dos lecturas **co-primarias**:
- **(i) Último token**, con la capa elegida por CV anidada.
- **(ii) Promedio sobre los tokens del Lean**, en una **capa fija a 2/3 de la profundidad, redondeada hacia abajo**.

## 5. Criterio de réplica por modelo
- **Permutaciones:** 1000, con la selección de capa incluida y con las particiones de las 5 semillas.
- **Valor p:** p < 0,05 con **corrección de Holm** sobre los 4 modelos nuevos × 2 lecturas, es decir, 8 pruebas.
- **Además:** el IC 95 % de **completo − apilado** tiene que quedar entero por encima de 0.

## 6. Afirmación global
Se afirma la réplica global si se cumplen las dos condiciones:
- **al menos 3 de los 4 modelos nuevos pasan**;
- el IC 95 % del **metaanálisis de efectos aleatorios** queda entero por encima de 0.

## 7. Filas dudosas, controles y secundarios
- **Las 44 filas dudosas** (`X-ni` en `probes/investigacion/scripts/clasificacion_200.tsv`) **entran en el primario**. El análisis sin ellas es de **sensibilidad**.
- **Controles añadidos:**
  - una línea base de **embeddings de texto** con un modelo disponible y de licencia abierta;
  - **Qwen3-4B con pesos aleatorios**, con la misma arquitectura y el mismo tokenizador.
- **Secundarios:** se reportan **sin corrección y rotulados como tales**. Entre ellos están todos los de la regla de las 12:55: 500 filas, misma capa, solo NL, NL desemparejado, superficie, P(Yes) y sin dudosas.

## 8. Código congelado
El código que se use desde aquí queda congelado. Los SHA-256 de `probes/referencia/probe_referencia.py` y de `probes/extraer.py` se anotan en el mismo registro de la bitácora que el de este archivo. Cualquier cambio posterior se anota como **desviación**, con su hora y su motivo.

## 9. Precisiones del orquestador (pendientes de confirmación de Carlos)
1. **Capa fija de la lectura (ii).** Es ℓ = ⌊2L/3⌋, donde L es el número de bloques del modelo (`num_hidden_layers`, en la config de texto si la config va anidada). El índice 0 son los embeddings y ℓ es la salida del bloque ℓ. Para Qwen3-4B (L = 36) da ℓ = 24. Para cada modelo nuevo, L se verifica en su `config.json` y se anota antes de extraer.
2. **Probe.** Es el mismo de la referencia: StandardScaler ajustado en el entrenamiento y regresión logística L2 con C = 1 e intercepto sin penalizar, resuelta hasta el óptimo. La CV anidada es la de `probe_referencia.py`: interna StratifiedGroupKFold(5) con la misma semilla que la externa; criterio, AUROC de los OOF internos; si hay empate, gana la capa más baja. La lectura (ii) no elige capa.
3. **Estadístico observado.** Es Δ sobre los puntajes OOF promediados por fila entre las 5 semillas, como en la regla de las 12:55.
4. **Permutaciones.**
   - Son 1000 barajes de y: el barajado p es `np.random.default_rng(p).permutation(y)`, con p = 0…999.
   - Las particiones externas **e internas** de las 5 semillas se calculan **una vez, con las etiquetas reales**, y se reutilizan. En cada permutación solo cambian las etiquetas. *Esto difiere de `probe_referencia.permutaciones`, que recalculaba las internas con la etiqueta barajada y usaba solo la semilla 0.*
   - Cada permutación repite el pipeline entero (lectura (i): selección de capa en completo y en solo_lean por separado; lectura (ii): capa fija) y calcula Δ_perm con el mismo promedio entre semillas.
   - El valor p es unilateral: p = (1 + #{Δ_perm ≥ Δ_obs}) / 1001.
5. **Solver de las permutaciones.** 1000 permutaciones × 5 semillas con selección de capa no caben en tiempo con `sklearn` lbfgs (≈ 170 h de CPU por modelo). Por eso se usa un solver exacto equivalente: Newton sobre el mismo objetivo, en la base de la SVD del entrenamiento estandarizado, en lote sobre las permutaciones. El **observado se calcula con el mismo solver** que el nulo.
   - **Requisito previo:** antes de usarlo sobre un modelo nuevo, se comprueba sobre Qwen3-4B (ya visto) que sus puntajes OOF reproducen los de `probe_referencia.py`, con un AUROC por condición igual a ±0,005.
   - Si no los reproduce, no se usa y se anota como desviación.
   - El script (`probes/referencia/prerregistro_v2_analisis.py`) se escribe después de este hash. Su SHA-256 se registra en la bitácora **antes** de correrlo sobre cualquier modelo nuevo.
6. **Holm.** Las 8 pruebas son los 4 modelos nuevos × las lecturas (i) y (ii), con α = 0,05 familiar. Qwen3-4B, Goedel, Kimina y Qwen3-8B no entran en la familia.
7. **Cuándo pasa un modelo.**
   - Una lectura pasa si su p ajustado por Holm es < 0,05 **y** el IC 95 % de completo − apilado, en esa misma lectura, queda entero por encima de 0.
   - Ese IC sale de un bootstrap de grupos estratificado por clase, con 2000 remuestreos y semilla 0.
   - El apilado es una regresión logística con C = 1 sobre los puntajes OOF internos de solo_lean y solo_nl, como en la referencia. En la lectura (ii), solo_nl usa su promedio sobre el NL en la misma capa fija.
   - **Un modelo pasa si pasa al menos una de sus dos lecturas.**
8. **Metaanálisis.**
   - Es DerSimonian–Laird sobre los Δ de los 4 modelos nuevos. El error estándar de cada modelo es la desviación estándar de su distribución bootstrap de Δ (bootstrap de grupos, 2000, semilla 0), y el IC 95 % es normal.
   - Se calcula por separado para cada lectura. La afirmación global exige que el IC quede por encima de 0 **en al menos una lectura**, y que esa lectura sea la misma en la que pasan al menos 3 modelos. Se reportan las dos.
9. **Línea base de embeddings.**
   - Modelo: `BAAI/bge-m3` (MIT), que ya está en caché local. `Qwen3-Embedding-0.6B` no está descargado.
   - Representación: vector denso (CLS normalizado) de los textos de completo y de solo_lean, sin plantilla de chat.
   - Análisis: mismo probe y mismas particiones. Se reportan AUROC(completo), AUROC(solo Lean) y su Δ.
10. **Pesos aleatorios.** `AutoModelForCausalLM.from_config` con `torch.manual_seed(0)`, sobre las mismas 4 variantes. Se analiza con el mismo pipeline y las mismas permutaciones si hay tiempo; si no, con el bootstrap solo.
11. **Vocabulario.** Se dice «separa» o «es decodificable linealmente». Nunca «el modelo sabe».
