# Regla de S7: Holm en la prueba central del Nivel B, e intervención sin los pares C2

Fecha: 13 de noviembre de 2026. Guion: `probes/intervencion/s7_sin_c2.py`, que todavía no existe y se escribe después de aprobar esta regla. Borrador para aprobación de Carlos Orrego-Franco.

**Estatus.** Las dos partes responden a observaciones de la revisión ciega del 13 de noviembre (`paper_adecuacion/v5_causal/revisiones/revisor_ciego_2026-11-13.md`, observaciones 6 y la sección 5). Son exploratorias y post hoc, y no forman parte del prerregistro del artículo. Ninguna corre un modelo.

Las dos partes no están en la misma situación, y la regla lo dice por separado:

- **Parte A (Holm).** El resultado ya se conoce. Los cuatro valores p están impresos en `tab:b`, y el revisor ciego y Claude ya calcularon a mano el ajuste (0.040, 0.059, 0.059 y 0.059). Esta parte no protege de mirar los datos: fija de dónde salen las cifras y cómo se reportan.
- **Parte B (sin C2).** Nadie ha calculado la AUROC pareada de P(Yes) bajo la intervención en un subconjunto de pares. Se conocen, y condicionan la pregunta, los resultados de S5 en los 377 pares, la brecha de las sondas sin C2 (`tab:bcontroles`, última columna) y que en C2 el control de superficie cruzada llega a 0.933.

## Parte A. Holm sobre los cuatro modelos

### A1. Pregunta

`tab:b` da un valor p de permutación por modelo y ninguno está corregido entre los cuatro. La pregunta es cuáles quedan por debajo de 0.05 tras la corrección.

### A2. Datos y medida

Los cuatro valores p de la diferencia en el último token, leídos de `probes/nivel_b/resultados/nivel_b_<modelo>_principal.json` (`permutaciones.diferencia.p`), para Qwen3-4B, OLMo-2, Llama-3.1 y Gemma-3. Se aplica el ajuste descendente de Holm sobre esa familia de cuatro pruebas, con monotonía forzada y tope en 1.

La familia son esos cuatro valores y nada más. No entra la segunda lectura, que no tiene prueba de permutación, ni los controles, ni las familias de edición.

### A3. Qué se reporta

Los cuatro valores ajustados, con tres decimales, en el pie de `tab:b` o en una frase junto a la tabla. Se dice cuántos quedan por debajo de 0.05.

### A4. Lo que no cambia

La regla del Nivel B decide por el intervalo de Δ con cinco semillas, no por el valor p. Los rótulos de `tab:b` («positive at reduced power», «null with upper bound») no cambian con Holm, y el artículo debe decirlo así. Tampoco cambia el recuento del resumen («three of four models»), que se refiere a esos intervalos, salvo que Carlos decida otra cosa al ver el texto.

### A5. Límites

La prueba usa 100 permutaciones, así que el menor p posible es 0.0099 y el menor ajustado posible es 0.040. La permutación usa el estadístico de la semilla 0 y la columna Δ es la estimación con cinco semillas; Holm no arregla esa diferencia.

## Parte B. La intervención sin los pares C2

### B1. Pregunta

En Qwen3-4B, los pares de la familia C2 (un numeral cambiado) se separan con rasgos de superficie tan bien como con las activaciones. La intervención de S5 baja la AUROC pareada de P(Yes) en los 377 pares. La pregunta es si esa caída se sostiene, frente a las direcciones al azar, cuando se dejan fuera los pares C2.

### B2. Datos

Los `pyes.npy` de S5, sin tocar: `probes/intervencion/resultados_s5/<modelo>/pyes.npy`, 54 condiciones, para los cuatro modelos. El subconjunto son los pares cuyo miembro inadecuado tiene una regla que no empieza por «C2» en `probes/nivel_b/datos/pares_indice_principal.jsonl`. Es la misma definición que usan `analizar_pares.py` y `analisis_s2_s3.py`, y deja 309 pares.

No se reestiman direcciones ni se vuelve a correr ningún modelo.

### B3. Medida

La de S5, restringida al subconjunto. P(Yes) es p(Yes) dividido por p(Yes) más p(No). La AUROC pareada se promedia dentro de cada origen y luego sobre los orígenes que conservan algún par. La caída de una condición es la AUROC sin intervenir menos la AUROC con esa condición. Los intervalos del 95 % salen de 2000 remuestreos de orígenes con semilla 0.

Se reporta, por modelo, en los 309 pares:

- la AUROC pareada sin intervenir, con el placebo y con el desplazamiento principal (f = 2) a lo largo de la dirección de diferencia de medias;
- la media y el máximo de la caída sobre las 20 direcciones al azar con f = 2;
- la caída menos la media al azar, con su intervalo;
- cuántas de las 20 direcciones al azar dan una caída igual o mayor.

Descriptivo, sin lectura:

- lo mismo en los 68 pares C2;
- en los 309 pares, la diferencia entre la dirección construida con `full` y la construida con `lean_only`, con su intervalo;
- en los 309 pares, la AUROC con f = 4 y f = 8.

### B4. Lectura, por modelo, fijada antes de calcular

El criterio es el de S5, aplicado a los 309 pares con f = 2:

- **«cumple sin C2»** si ocurren las dos cosas: el intervalo de la caída menos la media al azar queda por completo por encima de cero, y la caída supera a cada una de las 20 caídas al azar;
- **«no cumple sin C2»** en cualquier otro caso.

Casos señalados de antemano:

- Si la AUROC sin intervenir en los 309 pares tiene un intervalo que incluye 0.5, el modelo se reporta como «sin señal de partida» y su lectura no cuenta ni a favor ni en contra. Con los 377 pares Gemma-3 parte de 0.590.
- Llama-3.1 y Gemma-3 no cumplieron el criterio con los 377 pares. Si alguno lo cumple con 309, se reporta, pero no se cuenta como un modelo más que cumple: el subconjunto se eligió después de ver S5.
- Qwen3-4B sigue siendo post hoc, cumpla o no.

### B5. Qué se hace con el resultado

Salga lo que salga, los cuatro modelos se reportan en el apéndice `app:intervencion`, con una columna o una tabla pequeña y dos o tres frases.

- Si Qwen3-4B y OLMo-2 «cumplen sin C2», el cuerpo añade una frase en el párrafo de la intervención.
- Si alguno de los dos «no cumple sin C2», el cuerpo lo dice en ese mismo párrafo, junto al resultado de ese modelo, y la frase de lectura de la sección 7 se acota a los pares con numerales. El resumen no cambia sin que Carlos lo decida al ver las cifras.

### B6. Lo que la parte B no muestra

- No es la intervención repetida sin C2. Las direcciones de diferencia de medias se estimaron con todos los pares de entrenamiento, C2 incluidos. Un resultado positivo en los 309 pares no descarta que la dirección esté dominada por rasgos de numerales; solo muestra que mueve la respuesta en pares que no los cambian.
- Con 309 pares hay menos potencia que con 377. Un «no cumple» puede deberse a eso, y por eso se reporta el intervalo y no solo la lectura.
- El subconjunto se define con la etiqueta de familia del generador, no con una medida de superficie par a par.
- Vale lo dicho en S5 y S6: que el desplazamiento cambie la respuesta no muestra qué calcula el modelo.

## Aprobación

El guion solo calcula la parte B si existe `probes/intervencion/APROBADO_regla_S7` con el SHA-256 de este archivo. La marca la crea Carlos. Antes de eso el guion se puede escribir y probar con datos sintéticos, pero no leer ningún `pyes.npy` de S5.
