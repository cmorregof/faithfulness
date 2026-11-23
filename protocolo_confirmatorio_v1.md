# Protocolo confirmatorio sobre enunciados escritos después del piloto, v1

Texto del Apéndice «Borrador de un protocolo confirmatorio sobre enunciados escritos después del piloto» de la v7 de «It Compiles, but Is It What We Meant?» (`paper_adecuacion/v7_prosa/main_es.tex`), pasado a Markdown sin cambiar la hipótesis, la población, los datos, la instantánea, la réplica ni las verificaciones. Lo único que cambia es la frase sobre el efecto mínimo detectable, que el borrador dejaba pendiente. El cálculo está en la última sección. El hash SHA-256 de este archivo y la hora de su firma quedan en `probes/BITACORA.md`.

El piloto fija cuatro requisitos de una prueba limpia, y el protocolo que sigue está escrito para cumplirlos. El enunciado se mantiene constante y las etiquetas están certificadas por Lean. La comparación se hace con los dos controles de superficie, rasgos de superficie cruzada y n-gramas simples, y también con solo el código de Lean. Los enunciados son tales que los modelos no pueden haberlos visto.

**Hipótesis.** En Qwen3-4B, en el último token y con la capa elegida por validación cruzada anidada, la AUROC pareada de `full` supera a ambos controles de superficie y a la sonda que lee solo el código de Lean. Es decir, `full` menos superficie cruzada > 0, `full` menos n-gramas simples de los dos textos > 0 y Δ > 0, con cada intervalo por completo por encima de cero.

**Población.** Pares de las familias A, B y C3. Las ediciones de numeral se reportan por separado.

**Datos.** Enunciados añadidos a formal-conjectures después del 23 de octubre de 2026 (commit `c094b979`, la copia usada en el piloto), procesados con el generador y el certificador del piloto, congelados por hash. Por construcción ninguno estuvo en el piloto, y todos son posteriores al lanzamiento de cada modelo sondeado aquí.

**Instantánea.** 1 de noviembre de 2027, 00:00 UTC, prorrogada una sola vez hasta el 1 de febrero de 2028 si hay menos de 200 orígenes disponibles. La hipótesis exige que los tres contrastes salgan a la vez, con α = 0.025 unilateral en cada uno y sin corrección por multiplicidad, porque es una prueba de intersección y unión. Para una potencia conjunta de 0.8, el efecto mínimo detectable, igual en los tres contrastes, es de 0.088 a 0.104 con 300 orígenes y de 0.077 a 0.090 con 400. Detectar un efecto de 0.08 exige entre 362 y 502 orígenes. Los extremos de cada horquilla corresponden a correlación perfecta y a independencia entre los tres contrastes, porque el piloto no guardó los puntajes por fila con los que se estimaría esa correlación.

**Réplica.** El mismo contraste combinado sobre los cuatro modelos prerregistrados del Nivel A.

**Verificaciones.** 100 permutaciones dentro de cada par, una implementación independiente escrita a mano que debe coincidir dentro de 0.005 y llegar a la misma decisión, y una revisión humana a ciegas de las etiquetas.

## Cálculo de potencia

Calculado el 23 de noviembre de 2026 con la regla `probes/encargo_2026-11-23/regla_T3_protocolo_potencia.md`. Guion: `probes/encargo_2026-11-23/t3/potencia.py`. Salida: `t3/potencia.json`.

**Varianzas del piloto.** El error típico de cada contraste sale de su intervalo del 95 % en el piloto (Qwen3-4B, último token, 256 orígenes), como (superior − inferior) / 3.92, y se escala por √(256 / n):

| Contraste | IC 95 % del piloto | EE con 256 orígenes |
|---|---|---|
| `full` − superficie cruzada | [+0.058, +0.177] | 0.0304 |
| `full` − n-gramas | [+0.010, +0.141] | 0.0334 |
| Δ = `full` − `lean_only` | [+0.158, +0.291] | 0.0339 |

**Método.** Z_k ~ N(δ / EE_k, 1). El efecto mínimo detectable es el menor δ, en pasos de 0.001, con P(todos los Z_k > 1.96) ≥ 0.8. La correlación entre contrastes no se puede estimar con lo guardado del piloto. Con correlación positiva, que es lo esperable porque los tres comparten `full`, la potencia conjunta queda entre la de independencia (ρ = 0, la más baja) y la de correlación perfecta (ρ = 1, la más alta). Se añade ρ = 0.5 como punto intermedio, fuera de la regla.

**Comprobación.** Con un solo contraste (superficie cruzada) y 300 orígenes sale 0.079, la cifra de alrededor de 0.08 del borrador.

**Efecto mínimo detectable por número de orígenes**

| Orígenes | un contraste | dos controles, ρ = 1 / 0.5 / 0 | tres contrastes, ρ = 1 / 0.5 / 0 |
|---|---|---|---|
| 200 | 0.097 | 0.106 / 0.114 / 0.117 | 0.108 / 0.123 / 0.127 |
| 250 | 0.087 | 0.095 / 0.102 / 0.104 | 0.097 / 0.110 / 0.114 |
| 300 | 0.079 | 0.087 / 0.093 / 0.095 | 0.088 / 0.100 / 0.104 |
| 350 | 0.073 | 0.081 / 0.086 / 0.088 | 0.082 / 0.093 / 0.096 |
| 400 | 0.069 | 0.075 / 0.081 / 0.083 | 0.077 / 0.087 / 0.090 |
| 500 | 0.061 | 0.067 / 0.072 / 0.074 | 0.069 / 0.078 / 0.081 |
| 600 | 0.056 | 0.062 / 0.066 / 0.068 | 0.063 / 0.071 / 0.074 |

**Orígenes necesarios para δ = 0.08.** Un contraste, 290. Dos controles, de 351 a 422. Tres contrastes, de 362 a 502.

**Límite.** Los errores típicos vienen de un lote de desarrollo y suponen que la variabilidad por origen de los datos nuevos será la del piloto. El cálculo no usa los efectos observados en el piloto, que están inflados por la selección del análisis.
