# v5_causal: qué cambió respecto de v4_voz (13 nov 2026)

`main_en.tex` y `main_es.tex` salen de `v4_voz/` con `aplica_v5.py`, que aplica 16 pasajes por idioma. El antes y el después exactos, línea por línea, están en `cambios_v4_a_v5_en.diff` y `cambios_v4_a_v5_es.diff`. `v3_tmlr/` y `v4_voz/` no se tocaron.

## Comprobaciones

- `tablas_nivel_b.py --latex` coincide con cada `s5.json` a cuatro decimales y con todas las cifras de la propuesta. Las filas de las dos tablas nuevas las genera `aplica_v5.py` desde `tablas_nivel_b.json`.
- `verifica_v5.py` pasa en los dos idiomas: ninguna cifra de v4 desapareció; las 137 cifras nuevas distintas salen de `tablas_nivel_b.json`, de `ablacion.json` o del coseno mínimo de S1 (0.99939, escrito «at least 0.9993»); las claves nuevas son `tab:bcontroles2`, `tab:bintervencion`, `fig:bintervencion` y la cita `geometry`; las fórmulas, tablas y figuras de v4 son idénticas salvo los dos retoques aprobados en `tab:controles` y `tab:conjunta`.
- `coteja_en_es.py`: 112 bloques en cada idioma y las secuencias coinciden en todos.
- Resumen: 237 palabras en inglés y 247 en español, con las mismas cifras de v4 y las tres salvedades.
- `main_en.pdf` compila con `latexmk -pdf` (19 páginas, sin cajas desbordadas ni referencias sin resolver).
- `main_es.pdf` NO está compilado. Donde corrí todo falta el español de babel. El `.tex` en español sí compila con babel en inglés (prueba de estructura: 20 páginas, sin errores ni cajas desbordadas). Falta correr en el Mac: `cd ~/Personal/"Proyecto Godel"/paper_adecuacion/v5_causal && latexmk -pdf main_es.tex`. El archivo `main_es_ES_EL_DE_V4_recompilar.pdf` es el PDF viejo de v4 y se puede borrar.

## Pasajes

| # | Dónde | Antes | Después |
|---|---|---|---|
| 1 | Resumen | (no había) | Frase nueva tras la de los 377 pares: «At that level, shifting activations along the separating axis changes the model's answer more than random directions do in two of four models.» |
| 2 | Resumen | «The numbers are preliminary until they are compared with an independent hand-written implementation.» | Eliminada (sigue en el recuadro Pending) |
| 3 | Resumen | «We read this as a small signal with known confounds, and outline a confirmatory test…» | «We outline a confirmatory test…» |
| 4 | Contributions | cinco puntos | Punto 6, la intervención con sus dos incumplimientos |
| 5 | Related work | «…and make no causal claim.» | «We read our probing results under the warning in their title. The only causal evidence in this paper is the intervention at Level B, which meets its criterion in two of four models.» |
| 6 | Readouts | (no había) | Frase de S1 (coseno de al menos 0.9993) |
| 7 | `tab:controles` | siete filas | Fila «Combined» |
| 8 | The second readout | «Every control at Level B was computed against the last-token probe only, and none was computed for the second readout.» | «The controls above were computed against the last-token probe.» |
| 9 | Nivel B, texto nuevo | (no había) | «Controls at the second readout» con `tab:bcontroles2`; «Shifting the mean along the separating axis» con `tab:bintervencion` y `fig:bintervencion` |
| 10 | `tab:conjunta` | «n-grams of both texts, which only Qwen3-4B exceeds…» | «at the last token, n-grams of both texts…» |
| 11 | What the three levels say together | (no había) | Frase de lectura, tras la frase del Nivel B |
| 12 | Limitations, Method | «the evidence is correlational» | «their evidence is correlational» |
| 13 | Limitations, Method | «We have not intervened on any direction.» | «We intervened on one family of directions, at Level B only. The intervention meets its criterion in two of four models, and the run in Qwen3-4B is post hoc.» |
| 14 | Decisions after the fact | (no había) | Frase sobre los controles y las dos intervenciones, del 11 al 13 de noviembre |
| 15 | Conclusion | termina en «…an intervention along the probe direction could.» | Añade la frase sobre la intervención del Nivel B |
| 16 | Apéndice Deviations | termina en «9 Nov» | Entradas 11 Nov, 12 Nov (S2, sin cifras), 11–12 Nov y 12–13 Nov |

El español lleva los mismos 16 pasajes con el texto de la propuesta.

## Tres diferencias con lo aprobado

1. El paréntesis que cierra el segundo párrafo de la intervención dice «(Table… and Figure…)», para que la figura quede citada.
2. En el pie de `tab:bintervencion` la nota decía «bfloat16 does not reproduce exactly». «exactly» y «exactamente» están en la lista de giros prohibidos, así que quedó «bfloat16 arithmetic is not reproducible to the last digit» / «la aritmética en bfloat16 no se reproduce hasta el último dígito».
3. Formato: `tab:bcontroles2` usa 2pt entre columnas y `tab:bintervencion` va ajustada al ancho de línea, porque con 3pt se salían del margen 4 y 16 puntos.

## Anotaciones

- La regla de la réplica cita 0.689 para Qwen3-4B y el dato da 0.688. La regla no se corrige.
- Nivel A de Llama-3.1: `comprobacion_causal.json` no trae `tokens_lean_iguales_completo` porque el manifiesto de la extracción original no guardó `n_tokens_lean_*`. El coseno sí está (mínimo 0.99981) y la capa 0 difiere en 0.0.
- La figura de la intervención caía al comienzo de la página siguiente a su tabla. Resuelto en la quinta tanda (abajo).
- La figura ordena los modelos OLMo-2, Gemma-3, Llama-3.1, Qwen3-4B; las tablas siguen el orden de `tab:b`. Sin cambiar: ver la quinta tanda.

## Segunda tanda (13 nov, 07:34): resultados secundarios de la intervención

Aprobado por Carlos. `aplica_v5.py` aplica ahora 18 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 17 | Nivel B, párrafo de la intervención | termina la frase de Llama-3.1 en «…cannot be attributed to the statement.» | Añade: «In Gemma-3 the interval of the same difference also includes zero (+0.049 [−0.003, 0.100]). The secondary analyses are in Appendix…» |
| 18 | Apéndice nuevo `app:intervencion`, antes del borrador de protocolo | (no había) | Párrafo y tabla `tab:bsecundarios`: placebo, intercambio con la pareja, media común, dirección `full` menos `lean_only`, y si las dosis mayores superan a sus cinco direcciones al azar. Filas generadas desde `tablas_nivel_b.json` |

Comprobaciones tras la segunda tanda: `verifica_v5.py` pasa en los dos idiomas (la cota «within 0.02 of the base» del placebo se comprueba ahí mismo); `coteja_en_es.py` da 114 bloques por idioma con las mismas secuencias; `main_en.pdf` recompilado, 20 páginas, sin cajas desbordadas ni referencias sin resolver. `main_es.pdf` hay que volver a compilarlo en el Mac: el que hay es anterior a esta tanda.

El resumen no cambió: la frase «preliminary» sigue fuera, por decisión de Carlos.

## Tercera tanda (13 nov, 07:47): citas verificadas de la sección de la intervención

Carlos pidió aplicar los cambios que la evidencia permita y exija. Dos verificadores independientes (un Opus y un Sonnet) abrieron las fuentes primarias. `aplica_v5.py` aplica ahora 19 pasajes por idioma y `refs.bib` de v5 tiene cinco entradas nuevas, cada una con su línea `% verified`.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 19 | Related work | «…in five open-weight models and then test whether intervening…» | «…in five open-weight models and, in three of them, test whether intervening…» (las pruebas causales de Sudheendra y Srivastava cubren tres de sus cinco modelos) |
| 9a | Intervención, apertura | «A decodable label need not be used.» | Con cita a Elazar et al. (TACL 2021) |
| 9b | Intervención, fin del primer párrafo | (no había) | Las capas se intervienen en la misma pasada (comprobado en `intercambio.py`: un gancho por capa en una sola pasada), las direcciones al azar son vectores unitarios con desplazamiento del mismo tamaño; citas a Rimsky et al. (ACL 2024) y Elazar et al. |
| 9c | Intervención, nulo anterior | «The two interventions differ in the direction and in the operation.» | Añade el parentesco con el borrado lineal de conceptos (Ravfogel et al., ACL 2020; Belrose et al., NeurIPS 2023) y «…so the null cannot be attributed to the direction alone.» |
| 9d | Intervención, Marks y Tegmark | «…more causally implicated than those of logistic probes.» | «…in most of their conditions, in two LLaMA-2 models and with additive shifts.» |
| 11a | Frase de lectura | termina en «…does not hold in the other two.» | Añade: «A shift can also change the output through a pathway other than the one it targets» con cita a Makelov et al. (ICLR 2024) |

Makelov et al. lo propuso un solo verificador; lo abrí aparte (página de ICLR para título, cuatro autores y sede; arXiv para el resumen). La sede COLM 2024 de Marks y Tegmark solo se pudo confirmar en un espejo de OpenReview. Quedaron fuera Li et al. (NeurIPS 2023), Ravichander et al. (EACL 2021) y Belinkov (2022), cada uno propuesto por un solo verificador.

## Cuarta tanda (13 nov, 08:03): S6, masa de probabilidad en Yes y No

Regla `probes/intervencion/regla_S6_masa.md`, aprobada por Carlos a las 08:00 (SHA-256 b23eb692…) antes de calcular. Guion `masa_si_no.py`; no corre ningún modelo. Resultado en `resultados_s5/s6_masa.json`: en los cuatro modelos la lectura es «no se establece que pierda más masa que el azar». La masa sin intervenir es 1.000, 0.983, 0.989 y 1.000 (Qwen3-4B, OLMo-2, Llama-3.1, Gemma-3) y ninguna condición la mueve más de 0.001, tampoco con f = 4 ni f = 8. La medida está cerca de su techo.

En el artículo: una columna más en `tab:bsecundarios`, un párrafo en el apéndice `app:intervencion` y la entrada «13 Nov» en «Deviations». `verifica_v5.py` comprueba las cotas 0.982 y 0.001 contra el JSON.

## Quinta tanda (13 nov, 09:50): ajustes menores antes de la revisión ciega

Solo cambia la posición de un flotante. `aplica_v5.py` sigue aplicando 19 pasajes por idioma y ninguna frase ni cifra cambió.

- Figura de la intervención. Con `[!ht]` sola quedaba dentro del Nivel B en español, pero en inglés seguía en la página 12, encima del título del Nivel C. En `aplica_v5.py` la figura va ahora antes de `tab:bintervencion`, con `[!ht]`, en los dos idiomas. En inglés la figura queda en la página 11 y la tabla al comienzo de la 12; en español las dos quedan en la página 12. En ambos casos dentro del Nivel B.
- Orden de los modelos en la figura. No se cambió. El orden OLMo-2, Gemma-3, Llama-3.1, Qwen3-4B es deliberado: `fig_intervencion.py` lo anota como «el orden del artículo en las figuras» y coincide con el de `escaner_v3.MODELOS` y con el de `fig:b` (primero los modelos con regla previa, al final el exploratorio). Queda como pregunta para Carlos. Además, en el Mac falta `tueplots` en el python3 de Homebrew, así que regenerar la figura pide instalarlo antes.
- «Code and data». El párrafo dice: «The repository will be released with the preprint at \url{https://github.com/cmorregof}. It will contain the decision rules with their hashes and times, the certified pairs, the cross-surface features, and every result file cited here.» Lo prometido existe en local (`probes/` tiene las reglas con sus marcas `APROBADO_*`, la certificación del Nivel B y los resultados). El enlace apunta al perfil y no a un repositorio, y ni `probes/` ni `paper_adecuacion/` son todavía repositorios de git. El texto está en futuro, así que no promete nada falso hoy. No se reescribió; queda anotado para Carlos.
- `main_es.pdf` compilado en el Mac con `latexmk -pdf` (22 páginas, sin cajas desbordadas ni referencias sin resolver). Revisadas a ojo las páginas del Nivel B y el apéndice: las tres tablas nuevas caben en los márgenes y la figura y las referencias salen bien. `tab:bsecundarios` cabe porque va ajustada al ancho de línea, y con sus encabezados largos la letra queda muy pequeña en los dos idiomas.
- `fig:b`, que viene de v4, cae en inglés en la página 13, ya dentro del Nivel C (en español queda antes del título). Es un flotante de v4 y `verifica_v5.py` exige que las figuras de v4 no cambien, así que no se tocó.
- `verifica_v5.py` pasa en los dos idiomas; `coteja_en_es.py` da las mismas secuencias en todos los bloques; `main_en.pdf` tiene 20 páginas. Los dos `.diff` están regenerados.

## Sexta tanda (13 nov, tarde): P1 a P4 de la revisión ciega

Aprobado por Carlos («Aplica P1 a P4»). El informe del revisor y la tabla de observaciones están en `revisiones/revisor_ciego_2026-11-13.md` y `revisiones/tabla_y_cambios_2026-11-13.md`. `aplica_v5.py` aplica ahora 22 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 20 (P1) | Nivel A, «Decision» | «…so condition (b) is largely met.» | Añade cuatro frases: el apilado no alcanza a `lean_only` en la lectura (ii) (0.675, 0.678, 0.680 y 0.670 frente a 0.679, 0.688, 0.682 y 0.678), cómo se apila, `nl_only` en la capa fija (0.660, 0.643, 0.673 y 0.650) y que la condición (b) no es más estricta que una brecha positiva allí. Cifras leídas de `probes/referencia/v2_resultados_*.json` |
| 1 (P2a) | Resumen | «…in two of four models.» | «…in two of four models, one of them in a post hoc run.» En español, «uno post hoc» |
| 5 (P2b) | Related work | «…in two of four models.» | «…in two of four models, one of them post hoc.» |
| 15 (P2b) | Conclusion | «…in two of four models.» | «…in two of four models, one of them in a post hoc run.» |
| 11 (P2c) | What the three levels say together | «…the answer depends on the axis along which the second readout separates the classes.» | «…a shift along the axis on which the second readout separates the classes changes the answer more than the same shift along random directions.» |
| 9b (P3) | Intervención, primer párrafo | «The shift is applied at all those layers in the same forward pass, and the random directions are unit vectors given a shift of the same size.» | Seis frases: particiones de las medias de clase, signo por etiqueta de la fila, dónde actúan los ganchos, que el desplazamiento no se acumula, cómo se sortean las direcciones al azar, definición de P(Yes) y unidad del intervalo (256 orígenes). Comprobado en `intercambio.py` |
| 21 (P4) | Nivel B, «Construction», tras el primer párrafo | (no había) | Párrafo nuevo sobre qué certifica Lean: equivalencia con tácticas estructurales para la edición fiel, testigo numérico para la infiel, y solo con variables ℕ, ℤ, ℚ o ℝ. Fuente: docstring de `certificar.py` |
| 22 (P4) | Nivel B, «Construction» | «A review by a language model… found originals that were themselves not faithful… and edits that were equivalent in fact, and those 31 pairs were removed.» | Desglose: 31 pares retirados, 9 con original no fiel, 23 de la familia A «equivalentes de hecho», un par en los dos grupos. Conteos leídos de `probes/nivel_b/datos/exclusiones_nivel_b.json` |

Dos diferencias con lo propuesto:

1. La frase de P4 sobre la compuerta de superficie («…0.706, above its limit of 0.70») NO se aplicó. `compuerta_superficie_certificados.json` dice que el criterio que regía era «firma» (exceso sobre la tipicidad de 0.081 frente a un límite de 0.05) y no el «estricto» de 0.70. Los dos fallan, pero la frase propuesta nombraba el que no regía. Además, el 0.706 se midió sobre los 408 pares. Queda para que Carlos decida la redacción.
2. Resumen en español: «uno de ellos en una corrida post hoc» lo dejaba en 255 palabras y `verifica_v5.py` admite 250. Quedó «uno post hoc», con 250 justas. En el español de 2.1 y de la conclusión sí va la forma larga.

`verifica_v5.py` cambió: admite `\ref{tab:a}` en texto nuevo y toma como fuentes `v2_resultados_*.json` (lectura (ii) de los cuatro modelos de la réplica) y `exclusiones_nivel_b.json`. Pasa en los dos idiomas; `coteja_en_es.py` da 117 bloques por idioma con las mismas secuencias. `main_en.pdf` tiene 21 páginas y `main_es.pdf` 22, sin cajas desbordadas ni referencias sin resolver. La figura de la intervención sigue dentro del Nivel B en los dos; en español `fig:b` cae ahora en la página 14, ya dentro del Nivel C (flotante de v4, no se tocó).

## Séptima tanda (13 nov, tarde): compuerta de superficie

Aprobado por Carlos («con el criterio firma», «en dos frases»). `aplica_v5.py` aplica ahora 23 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 23 | Nivel B, «Construction», tras «…and the pairs were declared a development batch.» | (no había) | «A surface check fixed in advance also failed. On the 408 certified pairs, a logistic regression on unigrams and bigrams of the Lean alone reaches a paired AUROC of 0.706, an excess of 0.081 over an unsupervised baseline, against a limit of 0.05.» |

Las cifras se leen de `probes/nivel_b/datos/compuerta_superficie_certificados.json` (`n_pares`, `auroc_pareada_solo_lean`, `exceso_firma`, `umbral_firma`), y `aplica_v5.py` se detiene si el criterio registrado deja de ser «firma». `verifica_v5.py` toma ese JSON como fuente. Pasa en los dos idiomas; `coteja_en_es.py` da las mismas secuencias; `main_en.pdf` tiene 21 páginas y `main_es.pdf` 22, sin cajas desbordadas ni referencias sin resolver.

Sin resolver: el JSON registra que el criterio usado fue «firma», pero no cuándo se eligió frente al estricto. La frase hereda «fixed in advance» de la entrada del 6 Nov en «Deviations».

## Octava tanda (13 nov): lector simulado de la Residency, A1 y A2

Aprobado por Carlos («Sí, A1 y A2»). Los aplicó la sesión del lector de la Residency, coordinada con la del revisor ciego. `aplica_v5.py` aplica ahora 26 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 24, 25 (A1) | Resumen | «No level alone supports the claim…» era la penúltima frase, tras la de los mapas | La misma frase, sin cambios, pasa a cuarto lugar, tras «…and one reading the formalization alone.» Ninguna otra frase cambia |
| 26 (A2) | Final de «Contributions», tras la lista | (no había) | «Table~\ref{tab:conjunta} gives the status of the evidence at each level.» / «La Tabla~\ref{tab:conjunta} recoge el estado de la evidencia en cada nivel.» |

No entra ninguna cifra. El resumen sigue en 245 palabras en inglés y 250 en español, con las mismas cifras y las tres salvedades. `verifica_v5.py` cambió en una cosa: admite `\ref{tab:conjunta}` en texto nuevo. Pasa en los dos idiomas; `coteja_en_es.py` da 118 bloques por idioma con las mismas secuencias. `main_en.pdf` tiene 21 páginas y `main_es.pdf` 22, sin cajas desbordadas ni referencias sin resolver. Los dos `.diff` contra v4 están regenerados.

El origen de estos cambios y los que no se aplicaron están en `revisiones/resumen_lector_residency_2026-11-13.md`.

## Novena tanda (13 nov, tarde): P5, P6 y P8 de la revisión ciega

Aprobado por Carlos («Aplica P5 a P8»). `aplica_v5.py` aplica ahora 29 pasajes por idioma. P7 no se aplicó: sus seis retoques no estaban redactados y quedan propuestos en `revisiones/tabla_y_cambios_2026-11-13.md`, sección 6.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 27 (P5) | Pie de `tab:b`, antes de «By the rule…» | (no había) | «The rule decides on the interval of the five-seed estimate. The permutation $p$ is reported beside it and is not corrected across the four models.» |
| 28 (P6) | Nivel B, «Construction», párrafo nuevo justo antes de `tab:b` | (no había) | «Folds are grouped by source file, whereas the paired AUROC and the bootstrap take the origin as their unit. With the 189 source files as the unit instead, the gap is +0.229 [0.157, 0.301], +0.109 [0.046, 0.174], +0.086 [0.019, 0.158] and +0.037 [−0.038, 0.106], in the order of Table…» |
| 29 (P8) | «Deviations», entrada del 12 Nov | «…in any of the four models.» | Añade: «The models are Qwen3-4B, OLMo-2, Llama-3.1 and Gemma-3, and the gaps are +0.002 [−0.040, 0.049], −0.019 [−0.064, 0.028], +0.032 [−0.013, 0.077] and +0.008 [−0.041, 0.054].» |

Una diferencia con lo propuesto, en P6. La propuesta decía «Resampling the 189 source files instead gives…». En `analizar_pares.py` (`boot_p` con `ga`) el archivo es la unidad tanto del promedio como del remuestreo, y por eso el valor central difiere del de `tab:b`. La frase aplicada lo dice así: «With the 189 source files as the unit instead».

Fuentes: `probes/nivel_b/resultados/nivel_b_*_principal.json` (`secundarios.central_bootstrap_por_archivo.diferencia`, `n_archivos`) y `probes/sin_pregunta/resultados/s2a_*.json` (`sin_pregunta.delta_sp`). `verifica_v5.py` las toma como fuente, admite `\ref{tab:b}` en texto nuevo y trata `tab:b` como tabla de v4 con un retoque aprobado. Pasa en los dos idiomas; `coteja_en_es.py` da 119 bloques por idioma con las mismas secuencias; `main_en.pdf` tiene 21 páginas y `main_es.pdf` 22, sin cajas desbordadas ni referencias sin resolver. La figura de la intervención sigue dentro del Nivel B en los dos. En inglés `tab:bfam` y `fig:b`, que vienen de v4, caen en la página 13, ya dentro del Nivel C.

## Décima tanda (13 nov): pares de ejemplo del Nivel B (A3 del lector de la Residency)

Aprobado por Carlos («Sí, esa regla» y «Sí, las cuatro»). `aplica_v5.py` aplica ahora 30 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 30 (A3) | Nivel B, «Construction», tras «…C2 changes a numeral and C3 changes something else.» | (no había) | «Table~\ref{tab:bejemplos} shows one pair from each.» y la tabla `tab:bejemplos`: un par por familia (A, B, C2, C3) con enunciado, fragmento original, edición fiel y edición infiel |

Regla, fijada antes de mirar los pares: dentro de cada familia, el par con menos tokens editados (suma de `tokens_editados` de los dos miembros) y, en empate, el menor número de par en `pares_indice_principal.jsonl`. Salen los pares 15 (A, empatado con otros 45), 4 (B, con otros 31), 75 (C2, con otro) y 195 (C3, único).

Archivos nuevos: `ejemplos_nivel_b.py`, que aplica la regla y lee los textos del índice y de `pares_nivel_b.parquet` (se corre con `biblioteca/.venv/bin/python -I`; no usa ningún modelo), y `ejemplos_nivel_b.json`, su salida. `aplica_v5.py` arma las filas desde ese JSON; ninguna se escribe a mano. Los enunciados van literales y en inglés en los dos idiomas. El del par de C2 se corta tras su primera frase y el pie lo dice.

`verifica_v5.py` cambió: admite `\label` y `\ref` de `tab:bejemplos`, saca esa tabla del conteo de cifras (sus dígitos son texto Lean y enunciados citados) y comprueba aparte que la selección repite la regla, que los fragmentos son los del índice y que las filas del `.tex` son las del JSON. La idea de comprobarla así, en vez de admitir dígitos sueltos, fue de la sesión del revisor ciego. El enunciado contra el parquet lo comprueba `ejemplos_nivel_b.py` al generar el JSON, porque `verifica_v5.py` corre sin pyarrow.

Pasa en los dos idiomas; `coteja_en_es.py` da 119 bloques con las mismas secuencias; `main_en.pdf` tiene 21 páginas y `main_es.pdf` 22, sin cajas desbordadas ni referencias sin resolver. La tabla es la 3 y cae en la página 9 en inglés y en la 10 en español, así que las tablas siguientes suben un número. Los `.diff` contra v4 están regenerados.

Dos cosas que Carlos vio antes de aprobar y que quedan a la vista en la tabla: en el par 4 el original pide solo `0 < n` y el enunciado da 3 como respuesta, y en el par 75 la edición de C2 (`2 < m` por `3 < m`) es también una hipótesis más fuerte.

## Undécima tanda (13 nov, tarde): P7 de la revisión ciega, sin P7.5

Aprobado por Carlos («Aplica P7»). `aplica_v5.py` aplica ahora 36 pasajes por idioma. El texto exacto de cada retoque está en `revisiones/tabla_y_cambios_2026-11-13.md`, sección 6.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 31 (P7.1) | «Prompt variants», al final | (no había) | «Each variant has its own probe, so the `nl_mismatched` probe is trained and scored on the mismatched prompts.» |
| 32 (P7.2) | «Deviations», 5 Nov | «…in 1972 of its 2000 prompts.» | Añade: «The extraction covers the 500 rows of the benchmark in the four variants, and the analysis keeps the 450 that compile.» |
| 33 (P7.3) | Nivel A, «Decision» | «…with gaps of +0.046, +0.060, +0.060 and +0.030 [−0.006, 0.065]…» | Los cuatro intervalos: +0.046 [0.010, 0.082], +0.060 [0.025, 0.096], +0.060 [0.023, 0.095] y +0.030 [−0.006, 0.065] |
| 34 (P7.4) | Nivel C, «Result», al comienzo | (no había) | «The rule of this level calls the result positive if the interval of Δ, from a bootstrap over statements, lies entirely above zero.» |
| 35 (P7.4) | Nivel C, «Result» | «…gives +0.15354 [0.12102, 0.18714].» | «…gives Δ = +0.15354 [0.12102, 0.18714] in Qwen3-4B.» Comprobado: la cifra está en `resultados_c_qwen3_4b.json` y en `segunda_implementacion/resultado_c1.json` |
| 36 (P7.6) | «Where the separation is readable» | «…`nl_only` probes reach 0.61 to 0.74.» | «…in the four replication models.» |

P7.5 NO se aplicó. La frase propuesta decía que el tramo del enunciado en los mapas está en azar «by construction». Es falso tal como estaba redactada: esos tokens no dependen del Lean, pero el enunciado solo ya predice la etiqueta (`nl_only` de 0.61 a 0.74), así que nada garantiza el azar allí. El artículo ya lo dice bien en ese párrafo («where the model has not yet read the Lean… That does not mean the statement carries no information about the label»).

`verifica_v5.py` cambió: toma como fuente los intervalos de `sensibilidad_sin_dudosas`, el número de filas del manifiesto de DeepSeek-Prover-V2 (500) y el `n` de la réplica (450), y admite dos apariciones nuevas de `$\D$`. Pasa en los dos idiomas; `coteja_en_es.py` da 119 bloques por idioma con las mismas secuencias; `main_en.pdf` tiene 21 páginas y `main_es.pdf` 23, sin cajas desbordadas ni referencias sin resolver. La figura de la intervención sigue dentro del Nivel B en los dos.

## Duodécima tanda (13 nov): maquetación de `tab:bsecundarios` (A5 del lector de la Residency)

Aprobado por Carlos («Sí, haz A5 también»). `aplica_v5.py` aplica ahora 37 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 37 (A5) | Apéndice C, `tab:bsecundarios`, fila de encabezados | Cinco encabezados largos en una sola línea; `\resizebox` encogía toda la tabla hasta dejar la letra muy pequeña | Los mismos encabezados, con las mismas palabras, partidos en dos líneas con `\shortstack`. La tabla queda con letra de tamaño `\footnotesize` real |

No cambia ninguna celda, cifra ni pie. `verifica_v5.py` no cambió. Pasa en los dos idiomas; `coteja_en_es.py` da las mismas secuencias; sin cajas desbordadas ni referencias sin resolver. `main_en.pdf` pasa de 21 a 22 páginas porque la tabla ocupa más alto y el recuadro «Pending» del Apéndice D cae solo en la última; `main_es.pdf` sigue en 23. Los `.diff` contra v4 están regenerados.

`fig:escaner` no se tocó. El PDF de la figura mide 468 pt de ancho, que es el ancho de línea, así que ya entra a escala 1 y su texto va de 6.8 a 8.5 pt. Ampliarla en la página no es posible sin girarla, y girada tampoco gana tamaño porque es casi cuadrada. Hacerla más legible pide regenerarla con `escaner_v3.py` y letra mayor, que es cambiar una figura de v4 y necesita sus datos (`escaner_out/mapa_*.npz`) y su entorno. Queda a decisión de Carlos.

## Decimotercera tanda (13 nov, tarde): apéndice de prompts y controles

Aprobado por Carlos («Comprueba y aplica»). Responde a la observación 9 de la revisión ciega. `aplica_v5.py` aplica ahora 40 pasajes por idioma. El borrador y sus fuentes están en `revisiones/tabla_y_cambios_2026-11-13.md`, sección 7.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 38 | Preámbulo | (no había) | `\usepackage{upquote}`, para que los acentos graves del bloque literal salgan rectos. v4 no tiene ningún `verbatim`, así que no cambia nada más |
| 39 | «Prompt variants», al final | (no había) | «The exact prompts and the definitions of the controls are in Appendix…» |
| 40 | Apéndice nuevo `app:definiciones`, antes de `app:protocolo` | (no había) | Cuatro párrafos: el prompt `full` literal y sus variantes; el enunciado desemparejado; P(Yes); los controles de n-gramas, de superficie cruzada y combinado |

Tres cambios respecto del borrador, tras comprobar el código:

1. «Mismatched statement» ya no dice «At Level A». El esquema es el mismo en los tres niveles: el Nivel B llama al `main()` de `extraer.py`, y el Nivel C lo repite y completa la permutación con intercambios cuando el rechazo falla (`extraer_c.py`). El apéndice añade esa frase sobre el Nivel C.
2. «In Qwen3, with thinking disabled» pasó a «Thinking is disabled in the templates that offer that switch, those of Qwen3 and Goedel-Prover-V2». Comprobado en las plantillas de chat de la caché local: leen `enable_thinking` las de Qwen3-4B, Qwen3-8B y Goedel-Prover-V2-8B, y ninguna de las otras cinco.
3. «The three levels use the same templates» quedó como estaba, ya confirmado para los Niveles B y C.

Sin tocar: «Prompt variants» sigue citando la pregunta como «Is this formalization faithful?». El prompt real, que el apéndice da completo, añade «Answer Yes or No.»

`verifica_v5.py` cambió: admite la etiqueta y la referencia `app:definiciones` y dos fórmulas nuevas (`$C = 1$` y `$\neq$`). Pasa en los dos idiomas; `coteja_en_es.py` da 128 bloques por idioma con las mismas secuencias; `main_en.pdf` tiene 22 páginas y `main_es.pdf` 23, sin cajas desbordadas ni referencias sin resolver. El apéndice es el D y el borrador de protocolo pasa a ser el E.

## Decimocuarta tanda (13 nov): figura de los mapas rehecha (`fig:escaner`)

Aprobado por Carlos («Busca los mapas, si no reconstrúyelos, quiero que sean lo más legibles posibles» y «Sí, aplícala»). `aplica_v5.py` aplica ahora 41 pasajes por idioma.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 41 | `fig:escaner` | `\begin{figure}[t]` con `figuras_v3/escaner2d_modelos.pdf` (y `_es`) | `\begin{figure}[p]` con `figuras_v5/escaner2d_modelos_v5.pdf` (y `_es`). El pie no cambia |

**Datos.** Los `mapa_<modelo>.npz` que lee el guion de la figura no estaban en el Mac ni en Drive; se habían hecho en otra sesión. `figuras_v5/mapas_desde_escaner.py` los reconstruye desde las salidas crudas de `paper_adecuacion/escaner/<modelo>/` (puntajes fuera de partición por fila, capa y columna, y etiquetas): cada celda es la AUROC sobre las 450 filas. No corre ningún modelo. Quedan en `figuras_v5/escaner_out/`. Dos comprobaciones:

- El color de las 32 900 celdas coincide con el PNG de v3 que está en `v3_tmlr/paquete_v3.tgz` (diferencia máxima 0.004, el redondeo de la imagen a 8 bits).
- La diferencia media sobre los tokens de Lean en el 60 % superior de las capas reproduce las cinco cifras impresas en «Where the separation is readable» (+0.043, +0.039, +0.031, +0.024, +0.012), tomando como primera fila `round(0.4 L)`. El guion se detiene si alguna deja de coincidir.

**Figura.** `figuras_v5/escaner_v5.py` importa de `escaner_v3.py` la paleta, las rampas y el dibujo de las celdas, que siguen crudas. Cambia la disposición: figura de página completa (7.17 in de alto), filas un 26 % más altas y columnas un 15 % más anchas, nombre del modelo encima de su fila, eje de capas rotulado, marcador de la capa fija en los tres paneles, claves más grandes y ningún texto por debajo de 8 pt. La nota de cuatro líneas que iba dentro de la figura se quitó. Lo que no repetía el pie pasó a los rótulos: qué es Q/P y el tamaño del ruido de una celda (0.5 ± 0.045). Se pierde una frase, «About 5% of cells pass it by chance in each direction», que se deduce del 5–95 % del rótulo.

**Entorno.** El guion nuevo no usa LaTeX (al TeX del Mac le faltan cm-super y dvipng, que pedía el original); el texto va en Latin Modern desde los `.otf` de TeX Live. Necesita numpy, matplotlib, colorspacious y tueplots. Se generó con un entorno desechable en la carpeta temporal de la sesión; `biblioteca/.venv` no se tocó. Para regenerar: crear un entorno con esos cuatro paquetes y correr `mapas_desde_escaner.py` y luego `escaner_v5.py`.

`verifica_v5.py` cambió: admite que `fig:escaner` cambie de archivo y de `[t]` a `[p]`, y solo eso; exige que el resto del entorno, pie incluido, sea idéntico al de v4. Pasa en los dos idiomas; `coteja_en_es.py` da las mismas secuencias; sin cajas desbordadas ni referencias sin resolver. La figura cae en la página 9 en los dos idiomas, en página propia; `main_en.pdf` sigue en 22 páginas y `main_es.pdf` en 23. Los `.diff` contra v4 están regenerados. Los archivos de `figuras_v3/` no se tocaron.

## Decimoquinta tanda (13 nov): S7, Holm e intervención sin los pares C2

Regla `probes/intervencion/regla_S7_holm_sin_C2.md`, aprobada por Carlos a las 11:00 (SHA-256 a94cb1b0…) antes de calcular la parte B. Guion `s7_sin_c2.py`; no corre ningún modelo. Antes de calcular, el guion reprodujo con los 377 pares las cifras de S5 de `tablas_nivel_b.json`. Resultado en `resultados_s5/s7_sin_c2.json`.

- Parte A. Holm sobre los cuatro p de la diferencia en el último token: 0.040, 0.059, 0.059 y 0.059. Solo Qwen3-4B queda por debajo de 0.05. Este resultado ya se conocía al escribir la regla.
- Parte B. En los 309 pares sin C2 la lectura es la de los 377: «cumple sin C2» en Qwen3-4B y OLMo-2, «no cumple sin C2» en Llama-3.1 (una dirección al azar la iguala) y en Gemma-3 (seis). Ningún modelo quedó «sin señal de partida».

En el artículo (`aplica_v5.py` aplica ahora 45 pasajes por idioma), con el texto aprobado por Carlos y la variante «about the same»:

| # | Dónde | Antes | Después |
|---|---|---|---|
| 42 | Nivel B, párrafo de la intervención, tras la remisión al apéndice | (no había) | Seis frases: la preocupación de que el desplazamiento mueva un rasgo de superficie, que no se sostiene al apartar los pares de numeral, y el límite de que las direcciones se estimaron con esos pares |
| 43 | Pie de `tab:b` | «…and is not corrected across the four models.» | «Once corrected across the four models by Holm's method, only that of Qwen3-4B stays below 0.05, at 0.040; the other three rise to 0.059.» |
| 44 | Final de `app:intervencion` | (no había) | Párrafo «Without the numeral pairs» y tabla `tab:bsinc2` (base, desplazada, caída menos media al azar, direcciones al azar que la igualan). Filas generadas desde `s7_sin_c2.json` |
| 45 | «Deviations» | (no había) | Segunda entrada del 13 Nov, que dice que los valores de Holm ya se conocían al escribir la regla |

Dos diferencias con lo mostrado a Carlos:

1. Pidió «about the same» para el margen sobre la media al azar en el apéndice. Apliqué el mismo criterio a la frase paralela del cuerpo, que decía «as large as before» y quedó «about the same as before».
2. No se añadió `\citep{holm}` al pie de `tab:b`; Carlos no respondió a esa pregunta.

`aplica_v5.py` se detiene si las lecturas de `s7_sin_c2.json` dejan de ser las que describe la prosa. `verifica_v5.py` toma ese JSON como fuente, admite `tab:bsinc2` y dos `$p$` nuevos. Pasa en los dos idiomas; `coteja_en_es.py` da 130 bloques por idioma con las mismas secuencias; `main_en.pdf` tiene 23 páginas y `main_es.pdf` 24, sin cajas desbordadas ni referencias sin resolver.

Maquetación: en inglés la figura de la intervención abre la página 13, seguida de `tab:bfam` y del título del Nivel C. Sigue antes de ese título, pero ya no tiene prosa del Nivel B en su página. En español queda en la página 13 y el Nivel C empieza en la 14.

## Decimosexta tanda (13 nov, 13:42): introducción que explica el experimento, título y «Lean code alone»

Aprobada por Carlos por voz y confirmada en el chat a las 13:42, tras hablar con Fabián, a quien «the Lean alone» y la condición sin enunciado le resultaron difíciles de entender. `aplica_v5.py` aplica ahora 51 pasajes en inglés y 53 en español (el español lleva dos más por el recorte del resumen).

| # | Dónde | Antes | Después |
|---|---|---|---|
| 16.1 | Título | «Beyond the Lean Alone: …» / «Más allá del Lean solo: …» | «Beyond the Lean Code Alone: …» / «Más allá del código de Lean solo: …» |
| 16.2 | Introducción, fin del primer párrafo | termina en «…and is not the one intended.» | Añade: «The gap is now visible at scale. Of some 290 Lean-bearing papers in a recent batch of AI-generated mathematics, about 38 do not state the paper's main theorem \citep{xena2026checked}, and a proof checked in Lean need not match the written argument it accompanies \citep{bastounis2026lost}.» |
| 16.3 | Introducción, segundo párrafo nuevo | (no había) | Describe el experimento con el prompt literal («Is this formalization faithful? Answer Yes or No.»), dice que la respuesta se guarda como control, que la corrida se repite sin el enunciado, que esa segunda pregunta no tiene respuesta y que por eso la sonda mide lo que el código delata por sí solo |
| 16.4 | Introducción, tercer párrafo de v4 | «The difficulty is that the Lean text alone is informative. … \emph{relation} between the two texts.» | Eliminado: todo su contenido pasó al párrafo 16.3 |
| 16.5 | Todo el texto, pies incluidos | «the Lean alone» (15), «Lean text alone» (1 que quedaba), «el Lean solo» y sus contracciones (14) | «the Lean code alone» / «el código de Lean solo». La condición `\vr{lean\_only}` no cambia |
| 16.6 | Resumen en español | «…lo que delata el Lean solo», «…más allá del Lean solo», «…con enunciados en Lean posteriores…» | «…lo que delata el código de Lean», «…más allá del código de Lean», «…con enunciados posteriores…». Va sin «solo» y sin «en Lean» porque el resumen estaba en el máximo de 250 palabras. El inglés conserva «alone» y «Lean statements» |

Dos correcciones sobre el borrador que Carlos oyó por voz: decía «We do not use its answer», que es falso (P(Yes) es un control y es lo que lee la intervención), y añadía «the habits of the system that wrote it», que el artículo no afirma. Y la cláusula sobre Bastounis et al. quedó en lo que dice su resumen, porque el detalle de la cota (m + 4 frente a m + 5) no se comprobó en la fuente en esta sesión.

Referencias nuevas en `refs.bib`, con su línea `% verified`: `xena2026checked` (post del 12 nov 2026; autor «Xena Project», porque lo firma la cuenta del blog) y `bastounis2026lost` (arXiv 2610.08144, Bastounis, Circelli y Hansen, 6 oct 2026).

Verificador: las cifras 290 y 38 son del post citado y se excluyen del conteo solo dentro de esa frase, que debe aparecer exactamente una vez; los pies de tablas y figuras de v4 se comparan tras deshacer «code» / «código de». Pasa en los dos idiomas (resumen: 246 y 250 palabras). `coteja_en_es.py`: 130 bloques, mismas secuencias. `main_en.pdf` recompilado (23 páginas, sin cajas desbordadas ni referencias sin resolver). **`main_es.pdf` es anterior a esta tanda**: hay que compilarlo en el Mac.

Quedan sin cambiar: los rótulos dentro de las figuras ya dibujadas («Lean alone», «Lean-alone direction»), y cualquier documento fuera de esta carpeta que cite el título viejo.

## Decimoséptima tanda (13 nov, 13:48): cinco correcciones de texto

Aprobadas por Carlos en el chat («a todo sí»). `aplica_v5.py` aplica ahora 56 pasajes en inglés y 57 en español.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 17.1 | Pie de `tab:bintervencion` | «The base differs slightly from the stored P(Yes)… because the intervention runs in batches and bfloat16 arithmetic is not reproducible to the last digit.» | «The base was recomputed in the intervention run and differs from the stored P(Yes)… by up to 0.030, in Gemma-3.» La causa no se había comprobado y salió del pie. Diferencias: −0.001, −0.009, +0.001 y +0.030 |
| 17.2 | «Prompt variants» | «“Is this formalization faithful?”.» | «“Is this formalization faithful? Answer Yes or No.”», como en la introducción y en el Apéndice D |
| 17.3 | Controles nulos del Nivel A | «Neither produces it.» | «Neither produces a positive gap. Under readout (ii) with random weights and on the embeddings the gap is negative, with intervals below zero.» |
| 17.4 | «Limitations», «Method» | termina en «…the run in Qwen3-4B is post hoc.» | Añade: «One control was not run. Directions built as differences of means from shuffled labels would show how much of the effect comes from fitting a direction to these activations at all.» |
| 17.5 | Resumen en inglés | «…a confirmatory test on Lean statements written…» | «…on statements written…», para que diga lo mismo que el español |

Decisiones que Carlos cerró en el mismo mensaje, sin cambio de texto: todos los criterios se eligieron antes (el «fixed in advance» de la compuerta de superficie se queda); la cláusula de réplica del protocolo se mantiene. Encargos que pidió para Claude Code: repositorio público en GitHub con el README ya preparado, y rehacer las figuras con los rótulos nuevos («Lean code alone»).

`verifica_v5.py` pasa en los dos idiomas (resumen: 245 y 250 palabras); `coteja_en_es.py`: 130 bloques, mismas secuencias; `main_en.pdf` recompilado. `main_es.pdf` hay que compilarlo en el Mac.

## Decimoctava tanda (13 nov, 14:06): lo que salió de la lectura completa de la v5

Aprobada por Carlos en el chat («aplica todo lo que viste»), tras una lectura de corrido de `main_en.tex`. `aplica_v5.py` aplica ahora 62 pasajes en inglés y 63 en español.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 18.1 | Introducción, frase de Xena | «The gap is now visible at scale.» | «The problem is now visible at scale.» «Gap» es el término técnico del artículo y se define tres líneas después |
| 18.2 | Intervención, segundo párrafo | «Qwen3-4B meets it.» | «Qwen3-4B meets the criterion.» El antecedente había quedado a diez líneas |
| 18.3 | «Preregistration» | termina en «…and we record them as a deviation.» | Añade: «Both clauses were already in the document signed on 4 November.» Comprobado en `probes/prerregistros/prerregistro_v2_36bc53a4df4e.md`, puntos 7 («Un modelo pasa si pasa al menos una de sus dos lecturas») y 8 |
| 18.4 | Nivel C, segunda implementación | «+0.15354 [0.12102, 0.18714]» | «+0.154 [0.121, 0.187]», con tres decimales como el resto del artículo |
| 18.5 | «What the controls say» | «Gemma does not» | «Gemma-3 does not» |
| 18.6 | Todo el texto, pies incluidos | «the Lean» como sustantivo suelto (17) y «el/del/al Lean» (19) | «the Lean code» / «el código de Lean». No cambian «Lean tokens», «Lean text», «Lean statement(s)», «Lean formalization», «Lean block», «Lean~4» ni `\vr{lean\_only}` |

Sin cambio, por decisión de Carlos: el párrafo de los pares de numeral («A natural worry is…») conserva su tono conversado.

Siguen abiertos y no dependen de esta tanda: el recuadro «Pending» y «Use of AI tools» (cambian cuando `probe.py` esté comparado), la fecha de CriticLeanBench en «Contamination», «Code and data» (repositorio) y los rótulos dentro de las figuras.

`verifica_v5.py` pasa en los dos idiomas (el redondeo de 18.4 se comprueba ahí; resumen: 245 y 250 palabras); `coteja_en_es.py`: 130 bloques, mismas secuencias; `main_en.pdf` recompilado. `main_es.pdf` hay que compilarlo en el Mac.

## Decimonovena tanda (13 nov, tarde): repositorio y título

Aprobada por Carlos en el chat («Sí, aplícala»), después de ver el texto en los dos idiomas. `aplica_v5.py` aplica ahora 65 pasajes en inglés y 65 en español.

| # | Dónde | Antes | Después |
|---|---|---|---|
| 19.1 | Título en inglés y comentario de la línea 1 | «Beyond the Lean code Code Alone» | «Beyond the Lean Code Alone». La sustitución 18.6 («the Lean» → «the Lean code») había caído sobre el título ya corregido en la decimosexta tanda. El español no tenía el defecto |
| 19.2 | «Code and data» | «The repository will be released with the preprint at \url{https://github.com/cmorregof}. It will contain…» | En presente, con la URL `https://github.com/cmorregof/faithfullness` y el commit `ea66bad`. Añade la bitácora a lo que contiene y dice lo que no contiene: las activaciones extraídas y los textos de CriticLeanBench |
| 19.3 | Apéndice «Deviations and late decisions» | «…which will be released with the repository…» | «…which is in the repository (`probes/BITACORA.md`)…» |

**Repositorio.** `cmorregof/faithfullness`, privado al momento de esta tanda; hacerlo público es un paso que confirma Carlos. Primer commit `ea66bad`: 1002 archivos, 65 MB. Código bajo MIT; datos y texto bajo CC BY 4.0; `NOTICE.md` lista las fuentes y sus licencias. Fuera: activaciones, `direcciones.npz`, `revision_humana/` (con la clave de la revisión ciega), `prerregistro_v3_BORRADOR.md`, `probe.py`, `revisiones/`, los textos de CriticLeanBench, y de `nivel_b/` las carpetas `abiertos/`, `tripletas/`, `v3_previo/`, los `candidatos*.jsonl` y las revisiones hechas por modelos. Desde un clon de GitHub, `aplica_v5.py` reproduce los dos `.tex`, `verifica_v5.py` y `coteja_en_es.py` pasan y `latexmk` compila los dos PDF. El commit citado es el de los archivos de resultados; el texto con esta tanda entra en un commit posterior.

`verifica_v5.py` cambió en una cosa: el identificador del commit no cuenta como cifra, en la forma exacta `commit \vr{…}` y exactamente una vez. Sin ese cambio leía «66» dentro de `ea66bad` como cifra sin fuente. No detectaba el título duplicado; sigue sin comprobar el título.

`verifica_v5.py` pasa en los dos idiomas; `coteja_en_es.py`: 130 bloques, mismas secuencias; `main_en.pdf` (23 páginas) y `main_es.pdf` (24) compilados en el Mac, sin cajas desbordadas ni referencias sin resolver. Los dos `.diff` contra v4 están regenerados.

Siguen abiertos: los rótulos dentro de las figuras (las cuatro con LaTeX se regeneran idénticas a las actuales en un entorno desechable, comprobado píxel a píxel; faltan los rótulos aprobados), la frase de CriticLeanBench en «Contamination», el recuadro «Pending» y «Use of AI tools».
