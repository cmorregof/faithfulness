# `probe.py` frente a la referencia: Qwen3-4B, Nivel A (corrida del 22 nov 2026)

El nombre del archivo lleva la fecha del encargo (21 nov). La corrida se hizo el 22 nov, entre las 21:10 y las 21:20 de Bogotá.

**Resultado.** En las dos lecturas, las tres cantidades de `probe.py` quedan dentro de 0.005 de la referencia y el intervalo del 95 % de Δ cae del mismo lado del cero, por encima. El contraste completo frente a solo_lean es decodificable linealmente con las dos implementaciones.

| Lectura | Cantidad | `probe.py` | Referencia | Diferencia | ¿Dentro de 0.005? |
|---|---|---|---|---|---|
| (i) `ultimo`, capa anidada | AUROC(completo) | 0.8114 [0.7712, 0.8493] | 0.8143 [0.7716, 0.8524] | −0.0028 | sí |
| (i) | AUROC(solo_lean) | 0.7230 [0.6765, 0.7669] | 0.7230 [0.6764, 0.7683] | 0.0000 | sí |
| (i) | Δ | +0.0884 [0.0417, 0.1356] | +0.0913 [0.0428, 0.1366] | −0.0028 | sí |
| (i) | Decisión (IC de Δ respecto de 0) | por encima | por encima | | coincide |
| (ii) `media_lean`, capa 24 | AUROC(completo) | 0.7512 [0.7052, 0.7949] | 0.7510 [0.7046, 0.7964] | +0.0003 | sí |
| (ii) | AUROC(solo_lean) | 0.6552 [0.6047, 0.7040] | 0.6558 [0.6048, 0.7037] | −0.0006 | sí |
| (ii) | Δ | +0.0960 [0.0552, 0.1349] | +0.0952 [0.0571, 0.1343] | +0.0009 | sí |
| (ii) | Decisión (IC de Δ respecto de 0) | por encima | por encima | | coincide |

«La misma decisión» significa aquí lo que quedó escrito en la bitácora antes de correr: el intervalo de Δ cae del mismo lado del cero. `probe.py` no hace permutaciones ni control apilado, así que esto no reproduce el veredicto de «pasa o no pasa» del prerregistro v2.

## Capas elegidas en la lectura (i)

Cada fila es una semilla (0 a 4) y cada columna una partición externa.

| Semilla | completo | solo_lean |
|---|---|---|
| 0 | 36, 36, 26, 36, 36 | 36, 23, 35, 3, 36 |
| 1 | 36, 36, 36, 36, 36 | 23, 36, 29, 35, 23 |
| 2 | 36, 36, 23, 36, 36 | 3, 23, 36, 22, 23 |
| 3 | 36, 36, 36, 36, 36 | 22, 23, 16, 36, 35 |
| 4 | 36, 36, 36, 36, 36 | 35, 2, 23, 35, 36 |

En solo_lean las 25 capas coinciden con las de la referencia. En completo coinciden 24 de 25: en la semilla 2, partición 3, `probe.py` elige la capa 23 y la referencia la 36.

## Correlación fila a fila de los puntajes (450 filas)

| Lectura | Variante | Pearson | Spearman | Mayor diferencia absoluta |
|---|---|---|---|---|
| (i) | completo | 0.9979 | 0.9976 | 0.178 |
| (i) | solo_lean | 0.9999 | 0.9999 | 0.021 |
| (ii) | completo | 0.9998 | 0.9999 | 0.050 |
| (ii) | solo_lean | 0.9999 | 0.9999 | 0.053 |

El vector `y` de `probe.py` y el de los `.npz` de la referencia son idénticos, así que el orden de las filas es el mismo.

## Lo que no coincide del todo, y causas posibles vistas desde fuera

La única diferencia que se nota es AUROC(completo) en la lectura (i), −0.0028, que se traslada entera a Δ. No leí el código de la referencia. Desde fuera veo dos causas compatibles con los datos:

1. *La capa distinta.* En una de las 25 particiones externas las dos implementaciones eligen capas distintas (23 frente a 36). Eso cambia los puntajes de unas 90 filas en una de las cinco semillas y explica la diferencia máxima de 0.178 en un puntaje.
2. *El solver.* La bitácora (línea 446, 4 nov) anota que la referencia validó su «solver v2» contra sklearn en este mismo caso: 0.8143 con el solver v2 y 0.8114 con sklearn, con la capa igual en 24 de 25 particiones. `probe.py` usa sklearn y da 0.8114. Las dos cifras son las mismas que salen aquí.

En la lectura (ii) las diferencias son de menos de 0.001. Los intervalos difieren en la tercera cifra, lo que puede venir de cómo cada implementación estratifica o siembra el bootstrap.

## Barajadas (detector de fugas)

`control_barajadas` una vez, en `ultimo`, capas 12, 24 y 36, cinco barajes: media 0.491, 0.473 y 0.472, con desviación de 0.03 a 0.05; el rango de los quince valores es 0.41 a 0.55. Ronda 0.5 por debajo, sin señal de fuga.

## Cómo se corrió

- `probe.py` sin cambios: SHA-256 `bbdb16350b88494e7c1c6a0d5c51b3003ea41d690327378fb58f06dc697dc30f`, copiado del doc del Project `claude/probe_candidato_2026-11-21.py.md`.
- No se cambió ningún parámetro del análisis ni ninguna línea de `probe.py`.
- Tres desviaciones del encargo, anotadas en la bitácora antes de correr:
  1. La corrida fue en la máquina Linux (aarch64) que la app de Claude abre dentro del Mac, no en `biblioteca/.venv`. Versiones: Python 3.13.18, numpy 2.5.4, scikit-learn 1.9.1, scipy 1.18.1. numpy y scikit-learn son las de la referencia.
  2. Un solo hilo de BLAS (`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1`). La prueba corta dio puntajes idénticos bit a bit con uno y con cuatro hilos.
  3. `main` no se ejecutó entero, porque esa terminal corta cada orden a los 180 s. `corrida_probe_2026-11-21/correr_lecturas.py` (SHA-256 `117a81b7…38ac101e`) llama a las funciones de `probe.py` con los argumentos de `main`, una pieza por orden. No se corrieron las curvas de 37 capas, la superficie, P(Yes) ni el subconjunto de 500.
- Tiempo de cómputo: lectura (ii), 5 s; lectura (i), 10 corridas de 18 s más 4 s de cierre, unos 3 minutos; barajadas, 2 s.
- Los resultados de la referencia (`referencia/v2_resultados_qwen3_4b.json` y los dos `v2_puntajes_qwen3_4b_*.npz`) se abrieron solo después de que `salida/lectura_i.json`, `salida/lectura_ii.json` y los puntajes estuvieran en disco. Antes de la corrida ya se habían visto dos cifras de la referencia, por la línea 446 de la bitácora y por el encargo; está anotado en la bitácora.

## Alcance

Esta comparación cubre solo Qwen3-4B en el Nivel A. Los otros cuatro modelos prerregistrados y los Niveles B y C no se han comparado con `probe.py`.

Archivos: `corrida_probe_2026-11-21/salida/` (puntajes y resúmenes en JSON) y los registros `salida_*.log` de la misma carpeta.

Autoría del código: ______. Corrida: Claude, en la app de escritorio (no Claude Code), 22 nov 2026.
