# `probe.py` frente a la referencia: Nivel A en ocho modelos y Nivel C en dos (corrida del 22 nov 2026)

Encargo: `probes/ENCARGO_probe_todo_2026-11-22.md`. La corrida se hizo en el Mac de Carlos, entre las 22:08 del 22 nov y las 00:04 del 23 nov, hora de Bogotá. `probe.py` no se modificó: SHA-256 `bbdb16350b88494e7c1c6a0d5c51b3003ea41d690327378fb58f06dc697dc30f`.

## Resultado

Las cifras coinciden y una decisión no. `probe.py` se comparó con la referencia en 18 lecturas: las dos lecturas del Nivel A en ocho modelos y la prueba central del Nivel C en dos. En las 18, AUROC(completo), AUROC(solo_lean) y Δ quedan dentro de 0.005 de la referencia. La mayor diferencia es 0.0033.

La decisión, que es el lado del cero en que cae el intervalo del 95 % de Δ, es la misma en 17 de las 18. La excepción es Qwen3-8B en la lectura (i) del Nivel A. Ahí `probe.py` da Δ = +0.0457 [+0.0016, +0.0914] y la referencia +0.0429 [−0.0041, +0.0882]. La diferencia puntual es +0.0027, dentro de la tolerancia, pero el intervalo de `probe.py` queda por encima de cero y el de la referencia lo incluye. Con la regla escrita en la bitácora antes de correr, eso cuenta como un cambio de decisión.

Por esa excepción no se tocó el artículo ni el README, como manda el paso 5 del encargo. Al final de este informe queda la frase propuesta para que Carlos decida.

Los cuatro modelos prerregistrados del Nivel A coinciden en las dos lecturas, en cifras y en decisión. Qwen3-8B es un modelo exploratorio en el artículo, que ya reporta para él un intervalo que incluye el cero en la lectura (i).

El Nivel B no se comparó, porque su cifra principal es una AUROC pareada que `probe.py` no calcula.

## Qué se comparó y qué no

Se comparó el contraste central, Δ = AUROC(completo) − AUROC(solo_lean), con sus dos AUROC y el intervalo de Δ.

- **Nivel A.** 450 filas que compilan (250 y 200). Lectura (i): `ultimo`, capa por validación anidada. Lectura (ii): `media_lean`, capa fija ⌊2L/3⌋. Ocho modelos: Qwen3-4B, los cuatro prerregistrados (OLMo-2-7B, Gemma-3-4B, Llama-3.1-8B, DeepSeek-Prover-V2-7B) y tres exploratorios (Goedel-Prover-V2-8B, Kimina-7B y Qwen3-8B).
- **Nivel C.** Prueba central C1 de `nivel_c/regla_borrador.md`: las 3752 filas de ProofNetVerif, `ultimo`, capa por validación anidada, bootstrap de enunciados estratificado por tipo de grupo. Dos modelos: Qwen3-4B, que es el de la regla aprobada, y Llama-3.1-8B, exploratorio.

`probe.py` no hace permutaciones ni control apilado. Por eso esta comparación no reproduce el veredicto de «pasa o no pasa» del prerregistro v2, ni la corrección de Holm, ni el metaanálisis. La lista completa de lo que quedó sin comparar está más abajo.

## Nivel A

{{A_principal}}

En la columna de decisión, el primer rótulo es el de `probe.py` y el segundo el de la referencia. Los intervalos de las AUROC se dan para completar la tabla; la regla solo fija tolerancia sobre los valores puntuales y decisión sobre el intervalo de Δ.

### La lectura que cambia de decisión: Qwen3-8B, lectura (i)

El intervalo de Δ cruza el cero en la referencia por 0.004 y lo esquiva en `probe.py` por 0.002. Los dos límites inferiores están a menos de 0.005 de cero, que es la tolerancia de la regla, así que un desplazamiento de 0.003 en el valor puntual basta para cambiar de lado. Desde fuera, sin leer el código de la referencia, veo esto:

1. *La diferencia está en los puntajes de completo.* AUROC(completo) difiere en +0.0033 y AUROC(solo_lean) en +0.0006. En completo las dos implementaciones eligen la misma capa en 24 de las 25 particiones externas. En la que falta (semilla 0, partición 4), `probe.py` elige la capa 29 y la referencia la 22. En solo_lean coinciden las 25.
2. *El bootstrap no la explica.* Apliqué `diferencia_pareada` de `probe.py`, sin cambios, a los puntajes que la referencia guardó en su `.npz`. Da +0.0429 [−0.0010, +0.0876], que también incluye el cero. Con los mismos puntajes las dos maneras de remuestrear llegan a la misma decisión, así que el cambio viene de los puntajes (`salida/nivel_a/diagnostico_ic.json`).
3. *El solver es una causa compatible.* La bitácora (4 nov, 23:34) y `referencia/v2_validacion_solver_qwen3_4b.json` dicen que la referencia del Nivel A usa un «solver v2» propio, validado contra sklearn dentro de ±0.005 en Qwen3-4B, con la capa igual en 24 de 25 particiones. `probe.py` usa sklearn. Dos solvers que convergen a puntos algo distintos pueden ordenar distinto dos capas casi empatadas en la validación interna, y eso es lo que se ve aquí. No comprobé esta causa, porque hacerlo exige leer o ejecutar el código de la referencia.

Otras lecturas tienen el límite inferior del intervalo igual de cerca de cero y conservan la decisión. Por ejemplo, en Kimina (i) el límite de `probe.py` es +0.0013 frente a +0.0048 de la referencia, en Goedel (i) es +0.0055 frente a +0.0048 y en DeepSeek-Prover-V2 (i) es +0.0083 frente a +0.0084.

No ajusté ningún parámetro ni repetí nada con otra semilla.

### Capas de la lectura (i) frente a la referencia

{{A_capas}}

De las 400 selecciones de capa (ocho modelos, dos condiciones, 25 particiones), 385 coinciden. Las 15 que difieren están repartidas entre los ocho modelos, y en diez de ellas las dos capas son vecinas.

### Capas elegidas por `probe.py` en la lectura (i)

Cada celda es una semilla, con sus cinco particiones externas.

{{A_capas_elegidas}}

### Correlación fila a fila de los puntajes (450 filas)

{{A_correlacion}}

El vector `y` de `probe.py` y el de los `.npz` de la referencia son idénticos en los ocho modelos, así que el orden de las filas es el mismo. Las correlaciones más bajas, entre 0.989 y 0.999, aparecen en la lectura (i) y en la condición donde alguna partición eligió otra capa. En la lectura (ii), que no elige capa, ninguna baja de 0.9996.

### Barajadas (detector de fugas)

`control_barajadas` una vez por modelo, en `ultimo`, en las capas ⌊L/3⌋, ⌊2L/3⌋ y L, con cinco barajes.

{{A_barajadas}}

Las medias rondan 0.5, entre 0.455 y 0.515, sin señal de fuga.

### Qwen3-4B en el Mac frente a la corrida Linux del 21 nov

Los puntajes no coinciden bit a bit, pero las conclusiones son las mismas. Las 50 capas elegidas son iguales. Los resúmenes (AUROC, Δ e intervalos) difieren como mucho en 0.0005 y las barajadas en 0.0005. En los puntajes por fila la diferencia máxima es 0.0098 en la lectura (i) y 0.0053 en la (ii), con medianas por debajo de 0.0005. La causa probable es el BLAS: Accelerate en el Mac y OpenBLAS en la máquina Linux, con los mismos numpy 2.5.4 y scikit-learn 1.9.1.

| Lectura | Cantidad | Mac (22 nov) | Linux (21 nov) |
|---|---|---|---|
| (i) | AUROC(completo) | 0.8114 [0.7710, 0.8493] | 0.8114 [0.7712, 0.8493] |
| (i) | AUROC(solo_lean) | 0.7231 [0.6766, 0.7669] | 0.7230 [0.6765, 0.7669] |
| (i) | Δ | +0.0883 [+0.0415, +0.1351] | +0.0884 [+0.0417, +0.1356] |
| (ii) | AUROC(completo) | 0.7512 [0.7054, 0.7948] | 0.7512 [0.7052, 0.7949] |
| (ii) | AUROC(solo_lean) | 0.6552 [0.6048, 0.7040] | 0.6552 [0.6047, 0.7040] |
| (ii) | Δ | +0.0960 [+0.0550, +0.1348] | +0.0960 [+0.0552, +0.1349] |

El artículo cita hoy las cifras de la corrida Linux (+0.088 [0.042, 0.136] y +0.096 [0.055, 0.135]). Con la corrida del Mac los dos límites de la lectura (i) redondean a 0.041 y 0.135.

### `main` entero de Qwen3-4B

`probe.main` corrió una vez, entero, en 3239 s (54 minutos, un hilo, con otros cinco procesos en la máquina). Su informe y sus cuatro figuras están en `corrida_probe_todo_2026-11-22/main_qwen3_4b/`. Se llamó con `parquet_en_orden=True`, porque el parquet no trae columna `idx`, y con la ruta de salida en esa carpeta.

En las 450 filas `main` da las mismas cifras que la corrida por piezas: lectura (i) 0.811, 0.723 y Δ = +0.088 [0.041, 0.135], con las mismas 50 capas; lectura (ii) 0.751, 0.655 y Δ = +0.096 [0.055, 0.135]. Eso confirma que llamar a las funciones por separado no cambia nada.

`main` calcula además tres cosas que la regla de esta comparación no cubre. Las anoto porque la referencia guarda dos de ellas como secundarias en `v2_resultados_qwen3_4b.json`:

| Medida, 450 filas | `probe.py` | Referencia |
|---|---|---|
| P(Yes) completo | 0.699 [0.653, 0.745] | 0.699 |
| Superficie del Lean | 0.670 [0.621, 0.719] | 0.682 |
| Barajadas, máximo entre las 37 capas | 0.506 en `ultimo`, 0.525 en `media_lean` | |

P(Yes) coincide. La superficie difiere en 0.012. Las dos líneas de base no están definidas igual: `linea_base_superficie` de `probe.py` usa conteos de unigramas y bigramas más el logaritmo de la longitud, y el apéndice del artículo describe el control de la referencia con n-gramas binarios. Esta cifra no entra en la tolerancia, pero conviene que Carlos sepa que ahí las dos implementaciones no miden lo mismo.

En las 500 filas, que incluyen las 50 que no compilan, `main` da Δ = +0.112 [0.069, 0.155] en la lectura (i) y +0.127 [0.091, 0.163] en la (ii). La referencia v2 no tiene ese análisis, así que no hay con qué compararlo.

## Nivel C

{{C_principal}}

En el Nivel C las dos implementaciones dan los mismos puntajes, bit a bit, en los dos modelos. Las 3752 puntuaciones de cada condición son idénticas y las 100 capas elegidas también, así que las tres cifras puntuales coinciden en todos sus decimales. Lo único que difiere son los límites de los intervalos, en la tercera cifra, porque cada implementación sortea sus remuestreos a su manera. En Qwen3-4B el intervalo de Δ es [+0.1198, +0.1867] con `probe.py` y [+0.1211, +0.1871] con la referencia; en Llama-3.1-8B, [+0.0919, +0.1651] y [+0.0899, +0.1647]. Los cuatro quedan lejos de cero.

Esa identidad tiene una lectura que conviene tener presente. La regla del Nivel C (§4) fija el mismo probe que usa `probe.py`: StandardScaler y regresión logística de sklearn con C = 1. La identidad bit a bit indica además que la referencia corrió con el mismo BLAS, presumiblemente en este mismo Mac. Que los puntajes salgan idénticos dice que las dos implementaciones arman las mismas particiones, eligen las mismas capas y promedian igual. No es una comprobación independiente del ajuste numérico, porque las dos llaman al mismo solver. En el Nivel A, en cambio, la referencia usa un solver propio, y por eso allí las cifras difieren en la tercera o cuarta decimal.

La segunda implementación del Nivel C, la del agente independiente, da para Qwen3-4B 0.8321, 0.6786 y Δ = +0.1535 [+0.1210, +0.1871] (`nivel_c/segunda_implementacion/resultado_c1.json`, abierto después de la corrida). Las tres implementaciones quedan a menos de 0.0001 entre sí.

### Capas frente a la referencia

{{C_capas}}

### Capas elegidas por `probe.py`

{{C_capas_elegidas}}

### Correlación fila a fila de los puntajes (3752 filas)

{{C_correlacion}}

### Barajadas

{{C_barajadas}}

Con 3752 filas las barajadas quedan mucho más cerca de 0.5 que en el Nivel A.

## Nivel B: no se corrió

La cifra que el artículo reporta en el Nivel B es la diferencia de AUROC *pareada*. Es la probabilidad de que la variante fiel de un par puntúe por encima de su gemela infiel, promediada dentro del origen y luego entre orígenes, con bootstrap de orígenes y particiones agrupadas por archivo fuente (`nivel_b/regla_borrador.md` y sus precisiones del 5 nov). `probe.py` no la calcula. Su `auroc` es la AUROC global sobre filas, y `ic_bootstrap` y `diferencia_pareada` remuestrean un solo vector de grupos, estratificado por clase.

Para compararlo harían falta tres piezas que hoy no existen en `probe.py`:

1. Una función de AUROC pareada dentro del par, con empates en ½ y promedio por origen.
2. Un bootstrap de orígenes, sin estratificar por clase, para la AUROC pareada y para la diferencia entre condiciones.
3. Dos vectores de grupo distintos: el archivo fuente para las particiones y el origen para el estadístico. `particiones_agrupadas` y `elegir_capa_anidada` reciben uno solo.

Escribir ese código es decisión de autoría de Carlos, así que no lo escribí.

## Lo que no se pudo comparar y por qué

- **Nivel B entero.** Por lo dicho arriba: estadístico pareado, bootstrap de orígenes y dos agrupamientos. Tampoco la intervención, los controles de superficie ni las tripletas.
- **Nivel A, veredicto del prerregistro.** Las 1000 permutaciones, la corrección de Holm, el control apilado, la sensibilidad sin las 44 filas dudosas y el metaanálisis no están en `probe.py`.
- **Nivel A, controles nulos.** `qwen3_4b_aleatorio` y los embeddings bge-m3 no estaban en la lista del encargo y no se corrieron.
- **Nivel A, variantes con permutaciones de la lectura (i).** `referencia/v2_resultados_{olmo2_7b,dsprover2_7b}_perm_i.json` no se abrieron. La comparación usó `v2_resultados_<modelo>.json`, como pide el encargo.
- **Nivel C, Δ dentro del mismo enunciado.** Necesita una AUROC dentro de grupo que `probe.py` no tiene.
- **Nivel C, transferencia desde CriticLeanBench.** Necesita elegir la capa en un conjunto, ajustar ahí y puntuar otro. `main` no lo hace y armarlo sería lógica nueva.
- **Nivel C, controles.** Apilado, n-gramas de los dos textos, NL desemparejado, P(Yes), las 20 permutaciones de cordura y la posición `media_lean`, que la regla deja como secundaria y el artículo no reporta.
- **Curvas por capa, superficie y P(Yes) de los otros siete modelos del Nivel A.** `main` entero solo se corrió para Qwen3-4B.

## Tiempo y entorno

### Nivel A

{{A_tiempos}}

Los segundos son de reloj dentro de cada proceso. Qwen3-4B corrió solo; los otros siete corrieron de a cuatro, y desde las 22:15 compartieron la máquina con cinco procesos del Nivel C, así que sus tiempos no miden el costo aislado. La columna «Referencia abierta» es la hora en que `comparar_nivel_a.py` leyó el JSON y los `.npz` de la referencia de ese modelo.

### Nivel C

{{C_tiempos}}

En el Nivel C la columna de la lectura suma los segundos de CPU de las diez corridas de `elegir_capa_anidada`, que fueron en procesos separados, cinco a la vez.

**Total.** El cómputo duró 1 h 56 min de reloj, de las 22:08 a las 00:04. En tiempo de proceso fueron unas 11.6 horas: 1.9 del Nivel A (de 161 s en Qwen3-4B a 1560 s en Goedel), 0.9 del `main` entero y 8.7 de las veinte corridas anidadas del Nivel C (13262 s en Qwen3-4B y 18119 s en Llama-3.1-8B).

### Entorno

- Mac de Carlos: macOS 26.7.3, arm64, 10 núcleos, 24 GB. `biblioteca/.venv`: Python 3.13.13, numpy 2.5.4 con BLAS Accelerate, scikit-learn 1.9.1, **scipy 1.18.1**, pyarrow 26.0.1.
- `ps` a las 22:06 no mostró procesos pesados de Carlos, así que no hizo falta `nice`.
- **Hilos.** Un ajuste de `_ajustar_y_puntuar` con 360 filas y 2560 dimensiones tarda de 0.012 a 0.018 s con los hilos por defecto y lo mismo con `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1`, con puntajes idénticos (`cronometro_defecto.log`, `cronometro_un_hilo.log`). Con 3003 filas tarda cerca de 1 s en las dos condiciones. En este Mac no aparece la diferencia de 40 veces de la máquina Linux. Se corrió con un hilo por proceso y varios procesos a la vez.
- A las 22:37 el Mac estaba con batería, que bajó hasta 59 %. Carlos lo conectó hacia las 23:10 y no se interrumpió nada.

## Cómo se corrió

- **Regla antes de correr.** La regla del Nivel A y la del Nivel C están al final de `probes/BITACORA.md`, cada una escrita antes de su corrida, con los SHA de `probe.py` y de los archivos de orquestación. La entrada del Nivel A lleva la hora «22:10» y se escribió hacia las 22:08; la corrección está anotada en la entrada siguiente.
- **Orquestación.** `correr_nivel_a.py` (SHA-256 `c200d3b2…327e3d18`) y `correr_nivel_c.py` (`e9624ac9…7226f9ba`) llaman a las funciones de `probe.py` con los argumentos de `main`. El primero es una adaptación de `corrida_probe_2026-11-21/correr_lecturas.py`. El segundo solo carga los datos con `probe.cargar`, sin `subconjunto` ni `_verificar_conteos`, y llama a `elegir_capa_anidada`, `ic_bootstrap`, `diferencia_pareada` y `control_barajadas`. `correr_main.py` (`ab3699da…4b205429d9`) llama a `probe.main`.
- **Orden de lectura.** Para cada modelo, los resultados de la referencia se abrieron después de que sus salidas de `probe.py` estuvieran en disco. Las dos horas están en cada `comparacion.json`. Los comparadores (`comparar_nivel_a.py`, `comparar_nivel_c.py`) se niegan a abrir la referencia si faltan salidas.
- **Código que no se leyó.** `referencia/probe_referencia.py`, `referencia/prerregistro_v2_analisis.py` y los scripts de análisis de `nivel_b/` y `nivel_c/`, incluida la segunda implementación. Sí se leyeron las reglas, los manifiestos, los `meta.json`, y después de cada corrida los JSON y `.npz` de resultados.
- **Lo que se vio antes de tiempo.** Hacia las 22:12, al leer el artículo para identificar las cifras de los Niveles B y C, vi la tabla del Nivel A con los cuatro modelos prerregistrados y las Δ de los modelos de descubrimiento. A esa hora la cola del Nivel A corría desde las 22:11:21 con el orquestador ya fijado y solo estaban en disco las lecturas (ii) de cuatro modelos. Del Nivel C vi la tabla del artículo antes de correr, porque había que leerla para saber cuál era la cifra principal. De Qwen3-4B en el Nivel A ya se conocían las cifras por el informe del 21 nov. Todo está anotado en la bitácora antes de la corrida del Nivel C. Ningún parámetro se tocó.
- **Desviaciones.** Ninguna respecto de la regla. Dos decisiones de ejecución: los modelos corrieron en paralelo y no uno tras otro, y las diez corridas anidadas del Nivel C fueron en procesos separados. Ninguna cambia un número, porque cada proceso es independiente y determinista.

## Frase propuesta para el artículo (no aplicada)

El artículo y el README quedaron como estaban. Si Carlos decide actualizar los dos pasajes, propongo este texto, que dice lo que se comparó, nombra la excepción y conserva las frases ya confirmadas. Las cifras de Qwen3-4B son las que el artículo ya trae.

**Recuadro «Pending» de la sección 3, en inglés.**

> All numbers in this version come from the reference implementation. By the rule of the project, they become findings only after comparison with the first author's own hand-written implementation (`probe.py`). That comparison has been run for the gap Δ at Level A, in the eight models and under both readouts, and at Level C, in the two models. In every case both AUROCs and the gap agree with the reference within 0.005. The interval of the gap falls on the same side of zero in both implementations, or includes zero in both, in every case but one. The exception is Qwen3-8B under readout (i), where `probe.py` gives +0.046 [0.002, 0.091] and the reference +0.043 [−0.004, 0.088]. In Qwen3-4B at Level A, `probe.py` gives Δ = +0.088 [0.042, 0.136] under readout (i) and +0.096 [0.055, 0.135] under readout (ii), against +0.091 and +0.095 from the reference. `probe.py` runs no permutation test and computes no control, so the comparison does not cover the decision of the preregistration, the meta-analysis or the controls of any level. Level B has not been compared, because `probe.py` does not compute its paired AUROC. The same holds for the within-statement gap and the transfer of Level C. Those numbers remain preliminary. Level C also has a second implementation, written by a separate coding agent with no access to the first and starting from the same extracted activations. It reproduces the main result of that level.

**Recuadro «Pendiente», en español.**

> Todas las cifras de esta versión provienen de la implementación de referencia. Por la regla del proyecto, pasan a ser hallazgos solo después de compararlas con la implementación escrita a mano por el primer autor (`probe.py`). Esa comparación ya se hizo para la brecha Δ en el Nivel A, en los ocho modelos y con las dos lecturas, y en el Nivel C, en los dos modelos. En todos los casos las dos AUROC y la brecha coinciden con la referencia dentro de 0.005. El intervalo de la brecha cae del mismo lado del cero en las dos implementaciones, o lo incluye en las dos, en todos los casos menos uno. La excepción es Qwen3-8B en la lectura (i), donde `probe.py` da +0.046 [0.002, 0.091] y la referencia +0.043 [−0.004, 0.088]. En Qwen3-4B, en el Nivel A, `probe.py` da Δ = +0.088 [0.042, 0.136] en la lectura (i) y +0.096 [0.055, 0.135] en la lectura (ii), frente a +0.091 y +0.095 de la referencia. `probe.py` no hace pruebas de permutación ni calcula ningún control, así que la comparación no cubre la decisión del prerregistro, el metaanálisis ni los controles de ningún nivel. El Nivel B no se ha comparado, porque `probe.py` no calcula su AUROC pareada. Lo mismo vale para la brecha dentro del mismo enunciado y la transferencia del Nivel C. Esas cifras siguen siendo preliminares. El Nivel C tiene además una segunda implementación, escrita por otro agente de programación sin acceso a la primera y a partir de las mismas activaciones extraídas. Reproduce el resultado principal de ese nivel.

La última parte del recuadro en español debe conservar la redacción que ya tiene `main_es.tex`; aquí la parafraseo.

**Párrafo «Use of AI tools», la parte que cambia.**

> For the gap at Level A, in the eight models, and at Level C, in the two models, that comparison has been run and the two implementations agree within 0.005. They also agree on the side of zero on which the interval falls, except for Qwen3-8B under readout (i). An AI assistant executed `probe.py`, unchanged. For Level B and for the controls of every level the comparison is pending.

> Para la brecha en el Nivel A, en los ocho modelos, y en el Nivel C, en los dos modelos, esa comparación ya se hizo y las dos implementaciones coinciden dentro de 0.005. También coinciden en el lado del cero en que cae el intervalo, salvo en Qwen3-8B con la lectura (i). Un asistente de IA ejecutó `probe.py` sin modificarlo. Para el Nivel B y para los controles de todos los niveles la comparación sigue pendiente.

Tres cosas que Carlos tendría que decidir antes de aplicar este texto:

1. Si la excepción de Qwen3-8B se reporta así o si antes quiere mirar la causa en el código de la referencia.
2. Si la sección «A later exploratory model», que da +0.043 [−0.004, 0.088] para Qwen3-8B en la lectura (i), lleva una nota con la cifra de `probe.py`.
3. Si el ejemplo de Qwen3-4B conserva las cifras de la corrida Linux o pasa a las del Mac.

Cambio de plan del 22 nov a las 23:10: el repositorio publica solo `paper_adecuacion/v6_retorica`. Si Carlos aprueba el texto, los pasajes se registran como tanda nueva en `v5_causal/aplica_v5.py`, después se corre `python3 aplica_v6.py ../v5_causal .` dentro de `v6_retorica`, se compilan ahí los dos PDF y se copian a `faithfulness/paper_adecuacion/v6_retorica` solo `main_en.tex`, `main_es.tex`, los dos PDF y los `.bbl`. En el README se toca únicamente la sección «Status». En `verifica_v5.py` habrá que poner en `FORMULAS_NUEVAS["\\D"]` el número de Δ nuevas en modo matemático. Hoy espera 2, y con los pasajes editados a mano el 22 nov ya hay 3, así que `verifica_v5.py` falla desde antes de esta corrida. En el .tex, `probe.py` va como `\vr{probe.py}`, Δ como `$\D$` y los intervalos con `\ic{}{}`.

No se dejó bloque de `git add`, `git commit` y `git push`, porque nada se copió a `faithfulness/`.

## Archivos

Todo está en `probes/corrida_probe_todo_2026-11-22/`.

- `salida/nivel_a/<modelo>/`: `datos.json`, `lectura_i.json`, `lectura_ii.json`, `barajadas.json`, los puntajes (`puntajes_i.npz`, `puntajes_ii.npz` y las diez corridas anidadas por separado) y `comparacion.json`.
- `salida/nivel_a/diagnostico_ic.json`: el bootstrap de `probe.py` sobre los puntajes de la referencia.
- `salida/nivel_c/<carpeta>/`: lo mismo para la prueba central del Nivel C.
- `main_qwen3_4b/`: el informe y las figuras del `main` entero.
- Orquestación y comparación: `correr_nivel_a.py`, `correr_nivel_c.py`, `correr_main.py`, `comparar_nivel_a.py`, `comparar_nivel_c.py`, `diagnostico_ic.py`, las dos colas y sus registros.
- Este informe se arma con `armar_informe.py` a partir de `informe_plantilla.md` y de las tablas que `tablas_informe.py` saca de los `comparacion.json`. Ninguna cifra de las tablas generadas se escribió a mano.

Autoría del código de `probe.py`: Carlos. Corrida: Claude Code en el Mac de Carlos, 22 nov 2026.
