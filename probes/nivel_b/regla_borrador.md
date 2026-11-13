# Nivel B — BORRADOR de regla de decisión (no aprobado)

Borrador de Opus 1, 4 nov 2026. Escrito **antes** de que exista cualquier par certificado o activación del Nivel B. Pensado para ser coherente con la REGLA DE DECISIÓN del Nivel A (bitácora, 12:55) y sus precisiones (13:37). Implementación preparada: `probes/nivel_b/analizar_pares.py` (reutiliza sin modificar `probes/referencia/probe_referencia.py`). No corre sin la marca `APROBADO_regla_decision`.

## Pregunta

Dentro de un mismo problema (mismo NL), ¿las activaciones separan una formalización **infiel** de una **fiel**, ambas obtenidas con una edición mínima del mismo Lean original y certificadas por Lean, **más allá de lo que separa el Lean solo**?

Es la prueba que el Nivel A dejó pendiente: allí un positivo indicaba información más allá del Lean, no necesariamente la correspondencia NL–Lean. Aquí el NL es idéntico dentro del par, así que todo lo que distinga a la fiel de la infiel viene del Lean editado, y solo la condición «completo» puede contrastarlo con el NL.

## Datos

- **Principal**: pares (infiel, fiel) certificados (`reglas_generador.md` §6: fiel «equivalente»; infiel «no_equivalente», nivel 2 si la edición es de hipótesis y nivel ≥ 1 si es de la conclusión), emparejados por tamaño de edición con `generar.emparejar` (mismo origen, mismo intervalo de tokens 1–4/5–8/9–14/15–24/25+, preferencia por misma clase de objeto y zona; ≤ 2 pares por origen; sin D2, D3, D6, D7).
- Filas de entrenamiento: las variantes de los pares (y = 1 fiel, y = 0 infiel). Los originales sin editar se extraen y se puntúan aparte (control), no entrenan.
- Modelo principal: Qwen3-4B (misma revisión, plantilla y `enable_thinking=False` que el Nivel A; `meta.json` de la extracción). Réplicas con Kimina-7B y Goedel-8B: secundarias, mismo procedimiento.

## Tamaño mínimo (antes de mirar nada)

Unidad de remuestreo = origen. Con indicadores pareados (fiel > infiel), AUROC pareada ≈ 0,75 en completo y 0,65 en solo Lean, la desviación de la diferencia por origen es ≈ 0,50 si la correlación entre condiciones es r = 0,4 y ≈ 0,36 si r = 0,7. MDE aproximado (α unilateral 0,025, potencia 0,8) = 2,8 · DE / √n:

| orígenes | r = 0,4 | r = 0,7 |
|---:|---:|---:|
| 200 | 0,099 | 0,070 |
| 300 | 0,081 | 0,057 |
| 400 | 0,070 | 0,050 |
| 500 | 0,063 | 0,044 |

(Con 2 pares por origen la DE baja algo; la CV y el ruido de etiquetas la suben.)

- **Análisis principal confirmatorio** si hay **≥ 400 pares certificados en ≥ 300 orígenes** (MDE ≈ 0,05–0,08, coherente con el 0,05–0,07 del Nivel A).
- **200–399 pares** (o < 300 orígenes): se corre con la misma regla; un positivo vale pero se rotula «potencia reducida»; un nulo se reporta con la cota superior del IC.
- **< 200 pares**: no se corre el análisis principal; se amplía el generador (otras fuentes o `--todos`) y se vuelve a pedir aprobación.
- Estimación previa (sin Lean): ~450 pares en ~320 orígenes, probablemente menos.

## Procedimiento

- **Posición**: «ultimo» (principal); «media_lean» secundaria.
- **Capa**: por CV anidada, independiente en cada condición (criterio AUROC interno; empate → capa más baja), como en el Nivel A.
- **Particiones**: StratifiedGroupKFold(5) **agrupado por enunciado de origen** (hash del NL normalizado: todas las filas de un origen, incluido el original, caen en el mismo fold), semillas 0–4, idénticas en todas las condiciones.
- **Probe**: StandardScaler (solo entrenamiento) + regresión logística, C = 1,0, igual en todas las condiciones.
- **Estadístico pareado**: para cada par, w = 1 si la fiel puntúa más alto que la infiel (puntajes OOF promediados entre las 5 semillas), 0,5 si empatan, 0 si no; promedio dentro del origen; **AUROC pareada** = promedio sobre orígenes.
- **Prueba central**: AUROC_p(completo) − AUROC_p(solo_lean), IC 95 % por **bootstrap de orígenes** (2000 remuestreos, semilla 0).
- **Decisión**: **positivo** si el IC queda entero por encima de 0 (unilateral α = 0,025) y se cumple el tamaño mínimo; si no, **nulo** («no detectable con este tamaño», con el límite superior del IC como cota), con la misma tabla.
- **Permutaciones**: 100, cada una **intercambia al azar los roles dentro de cada par** (`np.random.default_rng(p)`), con las particiones de la semilla 0 (calculadas con las etiquetas reales) y la selección de capa incluida; p = (1 + #{nulo ≥ observado}) / 101 contra lo observado con la semilla 0, para completo y para la diferencia.

## Controles (se reportan; no deciden salvo que se diga)

1. **Barajadas**: las 100 permutaciones dentro del par.
2. **Solo Lean**: es la comparación central.
3. **Solo NL** (cordura): el NL es idéntico dentro del par, así que la AUROC pareada debe ser 0,5; si no lo es, hay un error en la tubería.
4. **NL desemparejado** (Lean del par con el NL de otro origen): debe parecerse a solo Lean.
5. **Superficie**: n-gramas binarios (1–2) del Lean y del NL + longitudes, mismas particiones (como la referencia del Nivel A); se reporta su AUROC pareada y completo − superficie con IC.
6. **Superficie cruzada NL–Lean** (nuevo; el riesgo propio de este nivel): numerales del Lean ausentes del NL, relaciones del Lean frente a palabras de relación del NL («at most», `\le`, «positive»…), solapamiento de letras, subíndices y `¬`. C2 deja un numeral ausente del NL en el 79 % de los casos; D8, en el 36 %. Se reporta completo − cruzada con IC. **Propuesta para Carlos**: que el positivo exija además que completo − cruzada no sea negativo (IC no entero por debajo de 0). Si no se acepta, queda como reportado.
7. **P(Yes)**: p_yes/(p_yes+p_no) tras «**Answer:» (como en el Nivel A); AUROC pareada y probe − P(Yes) con IC.
8. **Fidelidad ≠ verdad**: AUROC pareada en los pares con infiel **B** (variante verdadera si el original lo es) frente a los pares con infiel **A/C refutada** (variante falsa). Si el probe separa los pares B, no se limita a la falsedad. P(Yes) en ambos.
9. **Tamaño de edición**: AUROC pareada por intervalo de tokens; subconjunto con |Δ tokens| ≤ 1; pendiente de (puntaje fiel − puntaje infiel) sobre (tokens fiel − tokens infiel). Hay una asimetría conocida en el intervalo 1–4 (fieles ≈ 4 tokens, infieles ≈ 1–2).
10. **Original frente a fiel**: P(puntaje del original > puntaje de la fiel), con el probe del fold que contiene al origen. ≈ 0,5 si «haber sido editado» no es la señal.
11. **Subconjuntos preespecificados** (se reportan, no deciden): por familia (A, B, C), misma clase de objeto, misma zona, nivel 2, por fuente (FormalMATH-Lite / formal_conjectures), «media_lean», la misma capa en ambas condiciones no se calcula aquí (sí en el Nivel A).

## Qué cuenta como positivo / nulo

- **Positivo**: IC 95 % de AUROC_p(completo) − AUROC_p(solo_lean) entero por encima de 0, con ≥ 200 pares (≥ 400 y ≥ 300 orígenes para «confirmatorio»). Se describe como «las activaciones separan, dentro del mismo problema, la formalización infiel de la fiel más allá del Lean solo» o «es decodificable linealmente».
- **Nulo**: cualquier otro caso; se reporta la cota superior.
- **Señales de alarma** (se informan antes de interpretar): solo NL ≠ 0,5; superficie cruzada ≥ completo; original frente a fiel lejos de 0,5; p de permutación > 0,05 con IC positivo (discrepancia: se busca el error antes de reportar).

## Elecciones que esta regla no fija todavía (para Carlos)

- Si el control 6 (superficie cruzada) pasa a ser condición del positivo.
- Si se incluyen los pares con reglas de huella (D2, D3, D6, D7) en un análisis secundario.
- Si los 2 pares por origen se reducen a 1 (más simple, menos potencia).
- Réplicas: qué cuenta como réplica (en el Nivel A: diferencia puntual > 0 con el mismo procedimiento).

## Cambios del revisor (Fable, 2026-11-04)

Escrito sin ver ninguna activación ni resultado del Nivel B (no existen). Las mediciones de abajo son sobre el texto de `candidatos.jsonl`, en CPU, sin Lean ni modelos. Detalle en `probes/revision_fable_2026-11-04.md`.

1. **Nueva compuerta antes de extraer activaciones (propuesta como condición, no como control reportado).** Sobre los pares certificados, calcular la AUROC pareada de una regresión logística con unigramas y bigramas del Lean variante solamente (mismas particiones agrupadas). Hoy, sobre los 730 pares provisionales, da ≈ 0,85 (0,91 en pares con fiel D1, 0,83 con D8; 0,77 con los operadores de orden enmascarados): la identidad de la regla es legible en el Lean (ver `reglas_generador.md`, cambios del revisor, punto 1). Si la línea base supera un umbral fijado antes (propongo 0,70), se corrige el generador (composición D∘X, D1 solo en la dirección que quita `>`/`≥`, equilibrio de numerales 0/1/3 entre fiel e infiel) antes de gastar GPU. Si se extrae igual, hay que declarar en el informe que solo_lean parte cerca del techo y que la diferencia está comprimida.
2. **Control 6 (superficie cruzada): recomiendo que sea condición del positivo**, como propone el borrador. Medido hoy sobre los pares provisionales: `rasgos_cruzados` da AUROC pareada ≈ 0,66; el rasgo «numerales del Lean ausentes del NL» solo, ≈ 0,55; pero en los 115 pares C2~D1 ese rasgo marca a la infiel casi sin error, porque D1 no añade numerales. Reportar además completo − solo_lean **sin los pares C2** como subconjunto preespecificado.
3. **Particiones: agrupar por archivo fuente, no solo por NL.** 220 de los 472 orígenes con par comparten archivo con otro origen (hasta 12 por archivo); `a_2`, `a_3`, `a_5` de una misma sucesión OEIS son casi el mismo problema con la misma edición C2. Propuesta: grupo = archivo (`OEIS/24356`, `ErdosProblems/504`, `FormalMATH_lite[i]`) en los pliegues y en las permutaciones; bootstrap por origen (principal) y por archivo (sensibilidad).
4. **Control 3 (solo NL = 0,5)**: es exactamente 0,5 por construcción (prompts idénticos → activaciones idénticas → empate en todos los pares). Comprueba la tubería; no informa nada sobre el modelo. Decirlo así.
5. **Control 8 (fidelidad ≠ verdad)**: los pares con infiel B son ediciones de hipótesis y los A/C refutados son de conclusión; reportar el contraste dentro de cada zona o reconocer la confusión.
6. **Tamaño mínimo**: con los filtros propuestos en `reglas_generador.md` (NL sin restos de Lean, NL ≥ 60 caracteres, correlato de orden en A2/A3/B2/B3/C3) quedan 609 pares provisionales en 403 orígenes antes de certificar; la estimación de ~450 certificados baja en la misma proporción (~380). El umbral «confirmatorio» (≥ 400 pares, ≥ 300 orígenes) queda al borde; está bien que exista la rama «potencia reducida», pero conviene decidir ahora si se corre `--todos` para compensar.
7. **Coherencia con la regla de las 12:55**: los dos cambios declarados (bootstrap de orígenes en vez de grupos estratificados por clase; permutación de roles dentro del par en vez de barajar etiquetas) están justificados por el diseño pareado. Lo demás (C = 1, capa por CV anidada independiente, 5 semillas, posición «ultimo») coincide. No veo fuga en la selección de capa ni en las permutaciones (particiones de la semilla 0 con etiquetas reales, como en las precisiones de las 13:37).
8. **Réplicas (elección abierta)**: propongo el mismo criterio del Nivel A (diferencia puntual > 0 con el mismo procedimiento), con la nota de que Goedel-Prover-V2-8B parte de Qwen3-8B y no es una réplica independiente en cuanto a datos de preentrenamiento.

## Cambios del revisor — segunda pasada (Fable, 2026-11-04): aplicados en `analizar_pares.py`, `lanzar.sh`, `compuerta_superficie.py`

Lo que en la primera pasada eran propuestas queda implementado y pasa a formar parte de este borrador (sigue sin aprobar). Probado con datos sintéticos (`probar_analizar_sintetico.py`: corre de punta a punta en modo rápido; `solo_nl` da 0,5 exacto; los subconjuntos nuevos existen). Ningún número real.

1. **Compuerta de superficie (nuevo paso 3/5 de `lanzar.sh`, antes de extraer activaciones).** Sobre los pares certificados: AUROC pareada de una regresión logística con unigramas y bigramas del Lean variante solo (CV agrupada por archivo). Criterio **estricto**: ≤ 0,70; criterio **firma**: exceso sobre una línea base no supervisada de tipicidad ≤ 0,05. `lanzar.sh` se detiene (código 4) si no pasa. Medido en el emparejamiento provisional de v2: 0,771 (v1: 0,852); no pasa el estricto y, por lo explicado en `reglas_generador.md` (convención de Mathlib: la forma atípica delata la edición), no creo que pueda pasar sin perder la mayoría de los pares. **Carlos fija el criterio antes de aprobar.** En cualquier caso, el informe debe declarar el valor de la compuerta y el nivel absoluto de solo_lean como techo de la diferencia.
2. **Pliegues, CV interna y permutaciones agrupados por archivo fuente** (`archivo` del índice; 431 archivos para 618 orígenes en v2). Unidad del estadístico pareado y del bootstrap principal: el origen. Bootstrap por archivo: reportado como sensibilidad (`central_bootstrap_por_archivo`).
3. **Control 6 (superficie cruzada NL–Lean) es condición del positivo**: si el IC 95 % de completo − cruzada queda entero por debajo de 0, la decisión es «NULO (condición 6)» aunque completo − solo_lean sea positivo. Medida informativa en v2 (texto, sin activaciones): 0,73 de AUROC pareada; los pares C2∘D (numeral ausente del NL) son el caso que más la alimenta.
4. **Control 8 por zona**: `verdad_infiel_verdadera_{hipotesis,conclusion}` y `verdad_infiel_refutada_{hipotesis,conclusion}`, además de los globales.
5. **Subconjuntos preespecificados nuevos**: `sin_C2` (sin pares con numeral editado) y `pares_compuestos` (en v2, todos). Se reportan; no deciden.
6. **Tamaño mínimo**: con v2 hay 1111 pares provisionales en 618 orígenes (antes de certificar); los umbrales (≥ 200 para decidir; ≥ 400 pares y ≥ 300 orígenes para «confirmatorio») se mantienen. Si Carlos elige el lote restringido a D8 (226 provisionales), la rama «potencia reducida» es la esperable.
7. **Control 3 (solo NL)**: se describe como comprobación de la tubería (0,5 exacto por construcción), no como control del modelo.
8. **Lo que no cambia**: pregunta, posición «ultimo», capa por CV anidada independiente por condición, C = 1,0, 5 semillas, estadístico pareado, IC por bootstrap de orígenes (2000, semilla 0), permutaciones de roles dentro del par (100), decisión unilateral α = 0,025.
