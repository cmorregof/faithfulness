# Nivel C: REGLA DE DECISIÓN (BORRADOR, sin aprobar)

Borrador de Claude («Opus 2»), 4 nov 2026, ~16:40 Bogotá. Es un prerregistro aparte de la regla de las 12:55 (Nivel A, CriticLeanBench) y de sus precisiones de las 13:37, y sigue su lógica salvo donde se dice lo contrario. **Ningún probe corre sobre ProofNetVerif hasta que Carlos lo apruebe** creando `probes/nivel_c/APROBADO_regla_decision`; `probe_c.py` y `lanzar.sh --probes` se niegan a correr sin esa marca. Una vez aprobado, no se cambia después de ver resultados.

Hasta la aprobación, **nadie calcula ninguna métrica que use las etiquetas de ProofNetVerif**: ni AUROC, ni P(Yes) por clase, ni curvas. Sí se permite comprobar la extracción sin etiquetas: formas, finitud, truncados, masa de P(Yes)+P(No).

## 0. Por qué ProofNetVerif
DriftBench no tiene datos públicos. ShadowBench no publica formalizaciones ni etiquetas (ver `fuentes.md`). Queda ProofNetVerif (PAug/ProofNetVerif@91183e5b, MIT): 3 752 pares (NL, Lean) con etiqueta humana de equivalencia semántica y 361 enunciados, de los cuales 217 tienen predicciones de ambas clases.

## 1. Pregunta
- **C1:** con etiquetas humanas de otra fuente, sin juez LLM y con negativos naturales, ¿las activaciones de Qwen3-4B separan formalizaciones adecuadas de inadecuadas **más allá del Lean solo**?
- **C2:** ¿la dirección aprendida en CriticLeanBench **transfiere** a ProofNetVerif?

## 2. Diseño fijado: ambos análisis; C1 es el principal y C2 el secundario
- **Principal: C1, dentro del conjunto (CV agrupada).** Es la réplica literal de la prueba de las 12:55 con etiquetas de otra fuente. Responde lo que el Nivel C debe responder: si el positivo del Nivel A depende del proceso de etiquetado de CriticLeanBench (DeepSeek-R1 + revisión). Tiene más filas (3 752 frente a 450), pero el n efectivo son los 361 grupos (las predicciones de un mismo enunciado son casi duplicadas) y el efecto de diseño de §7 reduce la ganancia de potencia. *[revisor, 2.ª pasada: antes decía «más potencia: 3 752 filas y 361 grupos, frente a 450 y 450».]*
- **Secundaria con criterio propio: C2, transferencia** (entrenar en CriticLeanBench, evaluar en ProofNetVerif). Es más exigente, pero mezcla dos cosas: «la señal existe» y «la señal es la misma dirección pese a un cambio de dominio». Hay que cruzar de olimpiadas a libros de pregrado, de 55 % a 30 % de adecuadas y de `theorem <nombre> … := by sorry` a `theorem dummy … := sorry`. Un nulo en C2 sería ambiguo; por eso no decide.
- Solo C1 decide el Nivel C. C2 y los demás análisis se reportan con su criterio, pero no lo cambian. No hay corrección por multiplicidad, porque hay una sola prueba de decisión.
- (Si Carlos prefiere invertir el orden, el cambio es de una línea en esta sección y en el §8; debe hacerse **antes** de aprobar.)

## 3. Datos, modelo, posiciones
- **Filas:** las 3 752 (valid + test juntas). Ningún grupo cruza los dos splits; aquí no se usan como partición.
- **No hay información de compilación** (`compila` = null), así que no se puede repetir el filtro «solo las que compilan» de las 12:55 sin compilar Lean (compuerta 4). Las mal tipadas son negativas y probablemente fáciles para el Lean solo. Eso hace la prueba **conservadora**: favorece a solo_lean, el comparador.
  - Si antes de aprobar se decide compilar con Lean v4.8.0, se añade «solo las que compilan» como análisis **secundario**. Nunca reemplaza al principal.
- **Modelo:** Qwen/Qwen3-4B@1cfa9a7208912126459214e8b04321603b3df60c, bf16, en MPS.
- **Prompts:** las mismas plantillas que en el Nivel A (`extraer_c.py` = `extraer.py` con cambios mínimos; diff en `extraer_c.diff`), plantilla de chat y `enable_thinking=False`. El Lean es cabecera + predicción.
- **Posición principal:** «ultimo». «media_lean» es secundaria.
- **Etiqueta:** 1 = `correct` (adecuada); 0 = resto. Proporción: 1 142 / 3 752 = 30,4 %.
- **Grupo:** enunciado NL normalizado (NFKC, minúsculas, espacios), el mismo hash que en el Nivel A. Coincide 1:1 con el `id` de ProofNet. Tipos de grupo: 217 mixtos, 127 solo negativas, 17 solo positivas.

## 4. C1 (principal): CV agrupada dentro de ProofNetVerif
- **Probe:** el mismo que en la referencia de las 12:55, es decir, StandardScaler ajustado en el entrenamiento + regresión logística (lbfgs) con **C = 1,0 fijo**.
- **Capa:** se elige por CV anidada, de forma independiente en cada condición. Interna: StratifiedGroupKFold(5) sobre el entrenamiento del fold, con la misma semilla. Criterio: AUROC interno; si hay empate, la capa más baja. Se grafican todas las capas.
- **Particiones externas:** 5 folds de StratifiedGroupKFold por grupo, semillas 0–4. Son idénticas en todas las condiciones.
- **Prueba central:** Δ = AUROC(completo) − AUROC(solo_lean), sobre los puntajes OOF promediados por fila entre las 5 semillas.
- **IC 95 %:** bootstrap de grupos, 2 000 remuestreos, semilla 0, **estratificado por tipo de grupo** (solo positivas / solo negativas / mixto). Se remuestrea con reemplazo dentro de cada estrato el mismo número de grupos que hay en los datos.
  - **Cambio respecto a las 12:55:** allí cada grupo tomaba la etiqueta de su primera fila. Aquí el 60 % de los grupos tiene ambas clases, y ese esquema no tiene sentido.
- **Decisión:** **positivo** si el IC de Δ queda entero por encima de 0 (equivale a una prueba unilateral con α = 0,025). Si no, **nulo**, que se reporta como «no detectable con este tamaño», con el límite superior del IC como cota del efecto; nunca como «no hay efecto». Se reporta también la dispersión de Δ entre las 5 semillas.
- **Subconjuntos preespecificados (se reportan, no deciden)** *[revisor, 2.ª pasada]*: por `source` (libro: Rudin, Dummit–Foote, Munkres, …), por `split` (valid/test) y por tipo de grupo (solo positivas / solo negativas / mixto). Pendiente de añadir a `probe_c.py` (hoy no los calcula; no cambié su lógica).

### C1-dentro (secundario clave, con criterio propio)
- **AUROC dentro de grupo:** la fracción de pares (adecuada, inadecuada) **del mismo enunciado** en que la adecuada tiene el puntaje mayor (los empates cuentan ½). Se calcula sobre los 217 grupos mixtos, con los mismos puntajes OOF.
- **Δ_dentro** = AUROC_dentro(completo) − AUROC_dentro(solo_lean). IC por bootstrap de los grupos mixtos (2 000, semilla 0). «Positivo» si el IC queda entero por encima de 0.
- **Por qué importa:** dentro de un grupo el NL es fijo. Lo que gane completo sobre solo_lean dentro del grupo no puede venir de que el NL revele el problema ni su dificultad. Es lo más cercano a la correspondencia NL ↔ Lean que permite este conjunto: los grupos son casi pares mínimos naturales. solo_nl da 0,5 dentro de grupo por construcción, porque su prompt es idéntico en todo el grupo.

## 5. C2 (secundario): transferencia CriticLeanBench → ProofNetVerif
- **Entrenamiento:** las 450 filas de CriticLeanBench que compilan, con las activaciones ya extraídas en `probes/activaciones/qwen3_4b/` (mismo modelo y revisión; el script lo comprueba). Posición «ultimo»; condiciones completo y solo_lean.
- **Capa: se elige SOLO con CriticLeanBench.** Se calcula el AUROC OOF por capa con StratifiedGroupKFold(5) para cada semilla 0–4, se promedia entre semillas y se toma el máximo (si hay empate, la capa más baja). Ningún dato de ProofNetVerif interviene en ninguna elección: ni capa, ni C, ni escalado. El StandardScaler se ajusta con CriticLeanBench.
- **Ajuste final:** probe sobre las 450 filas en la capa elegida; luego se puntúan las 3 752 de ProofNetVerif.
- **Formato** *[revisor, 2.ª pasada]*: el probe de «completo» se entrena con prompts cuyo Lean es `theorem <nombre> … := by sorry` y se evalúa sobre `theorem dummy … := sorry` con cabecera `import Mathlib` + `open …`; el estilo de la cabecera forma parte del cambio de dominio de C2 (ver §9, «formato»), no de C1.
- **Prueba:** Δ_T = AUROC_PNV(completo) − AUROC_PNV(solo_lean), con el mismo bootstrap estratificado por tipo de grupo. «Positivo» si el IC queda entero por encima de 0.
- **También se reporta:** AUROC_T(completo) con su IC (¿supera 0,5?), Δ_T dentro de grupo, y el probe de completo aplicado a nl_desemparejado de ProofNetVerif (completo − nl_desemparejado). Las curvas por capa en ProofNetVerif se muestran solo como figura; no se usan para elegir.

## 6. Controles (en C1 salvo que se indique)
- **Etiquetas barajadas:** **20** permutaciones (barajado p con `np.random.default_rng(p)`), con la selección de capa incluida, particiones de la semilla 0 y una sola semilla, para completo y solo_lean. Valor p = (1 + #{nulo ≥ observado}) / 21; el mínimo es 0,048.
  - **Cambio respecto a las 12:55 (100):** con 3 752 filas, cada ajuste cuesta del orden de 8 veces más, y 100 permutaciones con selección de capa costarían del orden de 10 h de CPU. Es un control de cordura, no la prueba de decisión. «Pasa» si el AUROC observado supera el máximo del nulo. *[revisor, 2.ª pasada]* El p mínimo es 0,048; el informe lo llama «cordura», no «prueba». Si el observado no supera el máximo del nulo con un IC central positivo, se busca el error antes de interpretar (misma regla que en el Nivel B).
- **Solo Lean:** es el comparador de la prueba central. Además: solo_lean evaluado en la capa que eligió completo en cada fold («misma capa»).
- **Superficie:** unigramas y bigramas binarios del Lean + longitudes; para completo, también del NL (la misma implementación que la referencia). Se reporta completo − superficie, global y dentro de grupo.
- **P(Yes):** p_yes / (p_yes + p_no) tras el prefijo «**Answer:». Se reporta su AUROC y la diferencia sonda(completo) − P(Yes) con el mismo bootstrap. Si la masa media es < 0,5, se marca «no interpretable», como en la plantilla del Nivel A.
- **nl_desemparejado:** el Lean de la fila con el NL de otro grupo, dentro del mismo quintil de longitud del NL; semilla 0, nunca del mismo grupo. Con grupos grandes, el rechazo puro no encuentra desarreglo; `extraer_c.py` repara la permutación con intercambios (cambio 5 del diff, idéntico en CriticLeanBench). Se reporta completo − nl_desemparejado, global y **dentro de grupo**. Si completo ≈ nl_desemparejado dentro de grupo, la ganancia del NL no es de correspondencia.
- **solo_NL y apilado:** completo − apilado(solo_lean + solo_nl): regresión logística C = 1 sobre los puntajes OOF internos, como en la referencia. Se reporta global y dentro de grupo.
- **media_lean:** la misma prueba central en la segunda posición (secundaria).

## 7. Potencia (aproximada, Hanley–McNeil)
- Sin agrupamiento, con 1 142 positivas, 2 610 negativas, AUROC ≈ 0,75 y r = 0,4–0,7 entre condiciones: EE(Δ) ≈ 0,007–0,010, así que **MDE ≈ 0,02–0,03** (unilateral α = 0,025, potencia 80 %).
- Con 361 grupos de 10,4 filas de media, el efecto de diseño puede ser ≈ 3 (CCI ≈ 0,2, supuesto), y entonces **MDE ≈ 0,035–0,05**.
- C1-dentro (217 grupos mixtos) tiene menos potencia; no la estimo con rigor.
- Como referencia (no como hipótesis), la diferencia del Nivel A en Qwen3-4B fue +0,088.

## 8. Interpretación (fijada antes de ver nada)
| C1 | C2 | Lectura |
|---|---|---|
| + | + | La señal «más allá del Lean» se replica con etiquetas humanas independientes y la dirección transfiere entre fuentes. |
| + | nulo | Se replica, pero la dirección aprendida en CriticLeanBench no transfiere (dependiente del dominio o del formato). |
| nulo | + | Inesperado: se reporta tal cual y se revisa la implementación antes de interpretarlo. |
| nulo | nulo | No detectable en ProofNetVerif con este tamaño; el positivo del Nivel A queda sin réplica en otra fuente de etiquetas. |

- **Alcance:** un C1 positivo indica información más allá del Lean con otra fuente de etiquetas, no necesariamente la correspondencia NL ↔ Lean. Para eso miran C1-dentro, nl_desemparejado dentro de grupo, el apilado y el Nivel B.
- Nunca se dice «el modelo sabe».

## 9. Riesgos declarados
- **Contaminación (límite principal del Nivel C; fechas verificadas por el revisor el 4 nov 2026, URLs en `probes/revision_fable_2026-11-04.md`).** ProofNetVerif está en Hugging Face desde el 5 feb 2025 (última modificación 24 mar 2025; artículo 2406.07222: v1 11 jun 2024). Qwen3 se publicó el 28–29 abr 2025, sin corte de datos declarado. CriticLeanBench se subió a HF el 8 jul 2025 (posterior). Kimina-Prover Preview es del 15 abr 2025 y arXiv 2604.23135 (§4.3) afirma que «Kimina and DeepSeek-Prover-V2 have training data overlap with ProofNet»; Goedel-Prover-V2 (5 ago 2025) se ajusta desde Qwen3-8B y hereda la exposición de Qwen3. Consecuencia: los enunciados de ProofNet y los pares etiquetados de ProofNetVerif eran públicos antes de los tres modelos; los de CriticLeanBench, no. Un C1 positivo puede reflejar memorización de pares etiquetados; un C2 nulo, cambio de dominio o memorización asimétrica. Se reporta como límite principal, no como nota. *[revisor, 2.ª pasada: antes decía «No es verificable».]*
- **Etiquetas.** Un solo anotador, cada muestra anotada dos veces, sin acuerdo publicado ni descripción de cómo se combinaron las dos pasadas; mal tipados inválidos; en la duda, inválida (apéndice A.2 del artículo, verificado). Eso añade ruido de etiqueta, que reduce la potencia. La ficha de HF no nombra los modelos que produjeron las predicciones.
- **Negativos no compilables** mezclados (ver §3).
- **Formato** distinto entre conjuntos (afecta a C2, no a C1).

## 10. Implementación y ejecución
- **Extracción:** `zsh probes/nivel_c/lanzar.sh --solo_extraccion`. Son 15 008 pases, ≈ 1,7–3,1 h. No necesita aprobación.
- **Probes:** `zsh probes/nivel_c/lanzar.sh --probes` → `probes/nivel_c/probe_c.py`, que reutiliza sin cambios las funciones de `probes/referencia/probe_referencia.py`. Se niega a correr sin la marca. Costo de CPU no medido; estimo 3–8 h con 6 procesos. Probado de punta a punta solo con datos sintéticos (`--sintetico`).
- **Segunda implementación (fijado en el borrador por el revisor, 2.ª pasada; Carlos puede quitarlo antes de aprobar):** la regla de las 12:55 exige dos implementaciones independientes (probe.py y la referencia) que coincidan. Aquí igual: C1 no se reporta hasta que una segunda implementación (probe.py adaptado por Carlos, o un agente independiente que no vea `probe_c.py`) lo reproduzca dentro del ruido de semilla.
- **Control sintáctico sin Lean (propuesto; no implementado en `probe_c.py`):** indicador barato de mala formación (paréntesis desbalanceados, identificadores ausentes de la cabecera) reportado junto a «superficie», porque los negativos no compilables favorecen a solo_lean (§3). No sustituye a compilar.

## Cambios del revisor (Fable, 2026-11-04)

Revisión independiente, sin activaciones ni métricas con etiquetas de ProofNetVerif. Verifiqué fuentes el 4 nov 2026 (URLs en `probes/revision_fable_2026-11-04.md`). No cambié el diseño; corrijo y preciso.

1. **§9, contaminación: «no es verificable» es demasiado fuerte; las fechas sí se verifican y el riesgo es asimétrico y concreto.** ProofNetVerif en Hugging Face: commit inicial 5 feb 2025, última modificación 24 mar 2025 (historial de commits); artículo arXiv 2406.07222 v1 11 jun 2024, v2 11 feb 2025, v3 29 oct 2025. Qwen3 se publicó el 28–29 abr 2025 (informe técnico 2505.09388, 14 may 2025), sin corte de datos declarado. CriticLeanBench: commit inicial en HF 8 jul 2025 (posterior a Qwen3). Kimina-Prover Preview: 15 abr 2025 (2504.11354); Goedel-Prover-V2: 5 ago 2025 (2508.03613), ajustado desde **Qwen3-8B**, así que hereda la exposición de Qwen3. arXiv 2604.23135 (v2, 17 may 2026), §4.3, afirma que «Kimina and DeepSeek-Prover-V2 have training data overlap with ProofNet». Conclusión: los enunciados de ProofNet y las etiquetas de ProofNetVerif eran públicos antes de los tres modelos; los de CriticLeanBench, no. Un C1 positivo con Qwen3-4B puede reflejar memorización de pares etiquetados; un C2 nulo, cambio de dominio o memorización asimétrica. Hay que decirlo como límite principal del Nivel C, no como nota.
2. **§0 y `fuentes.md`, etiquetas**: confirmado en el apéndice A.2 del artículo: «This annotation process was conducted by a single annotator», «Each sample has been annotated twice», «Ill-typed statements» marcados inválidos de inmediato, y «In case of doubts, the prediction was marked as invalid». No se publica cómo se combinaron las dos pasadas ni acuerdo alguno. La ficha de HF no nombra los modelos que produjeron las predicciones; la lista de `fuentes.md` (Llama3-8B, Llemma, GPT-4o…) es la de los modelos evaluados en el artículo, no una atribución por fila. La fecha «15 jul 2025 (HF)» de Goedel-Prover-V2-8B que da `fuentes.md` no la pude verificar (el artículo es del 5 ago 2025).
3. **§2, «tiene más potencia: 3 752 filas y 361 grupos»**: el n efectivo son los grupos (y, dentro de grupo, predicciones casi duplicadas del mismo modelo); §7 ya lo reconoce con el efecto de diseño. Reescribir la frase para no sugerir 8 veces más potencia.
4. **§6, permutaciones**: 20 permutaciones dan p mínimo 0,048; está bien como cordura si el informe lo llama así y no «prueba». Añadir: si el AUROC observado no supera el máximo del nulo, se busca el error antes de interpretar (como en el Nivel B).
5. **§4, subconjuntos preespecificados que faltan**: por `source` (libro: Rudin, Dummit–Foote, Munkres, …), por `split` (valid/test) y por tipo de grupo. Se reportan, no deciden.
6. **§3, negativos no compilables**: de acuerdo con que favorece a solo_lean. Añadir como control de superficie barato un indicador sintáctico sin Lean (paréntesis desbalanceados, identificadores inexistentes en la cabecera, `sorry` fuera de lugar), reportado junto a «superficie»; no sustituye a compilar.
7. **§5, C2**: la elección de capa y el escalado solo con CriticLeanBench están bien y no hay fuga. Falta decir que el probe de «completo» se entrena con prompts cuyo Lean es `theorem <nombre> … := by sorry` y se evalúa sobre `theorem dummy … := sorry`; el estilo de la cabecera es parte del cambio de dominio (ya está en §9, «formato»; enlazarlo aquí).
8. **§10, segunda implementación**: de acuerdo; es la misma exigencia de la regla de las 12:55 y conviene fijarla antes de aprobar.
9. **Compatibilidad de etiquetas con CriticLeanBench (pregunta del revisor)**: comparables en el concepto (adecuación semántica NL ↔ Lean juzgada por humanos), no en el proceso (sin juez LLM, duda = inválida, mal tipados incluidos, 30 % frente a 55 % de positivas, pregrado frente a olimpiadas). DriftBench no tiene datos públicos y ShadowBench no publica formalizaciones ni etiquetas (según `fuentes.md`; no lo volví a comprobar), así que no aplican. Lo correcto es presentar el Nivel C como réplica con **otra** fuente de etiquetas, no como la misma medida en otro conjunto.
