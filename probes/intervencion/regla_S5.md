# Regla S5. Desplazamiento a lo largo de la diferencia de medias (Nivel B, Qwen3-4B)

Fecha: 11 de noviembre de 2026. Guion: `probes/intervencion/intercambio.py`. Borrador para aprobación de Carlos Orrego-Franco.

**Estatus.** Análisis exploratorio y post hoc. Se escribe después de conocer S3 y S4. No es una réplica, no forma parte del prerregistro y por sí solo no sostiene ninguna afirmación del artículo.

## 1. Pregunta

S3 mostró que, en los pares mínimos del Nivel B, la etiqueta es decodificable linealmente de la media sobre los tokens de Lean por encima de los controles de superficie y del P(Yes) del propio modelo. S4 quitó una dirección y el P(Yes) no cambió más que con una dirección al azar. Queda abierta una pregunta más estrecha: si la media sobre los tokens de Lean se mueve hacia la clase contraria a lo largo del eje que separa las clases, ¿cambia la respuesta del modelo más que con un movimiento igual en una dirección cualquiera?

## 2. Datos y direcciones

- Los 377 pares certificados del Nivel B (754 filas, 256 orígenes), modelo Qwen3-4B, prompt `full` con la pregunta, lectura de P(Yes) tras el prefijo «**Answer:».
- Las mismas cinco particiones por archivo fuente (semilla 0). Las direcciones se estiman solo con las filas de entrenamiento de cada partición, y cada fila se interviene con direcciones que no la vieron. Las dos filas de un par caen siempre en la misma partición.
- Por capa y partición, con las activaciones guardadas (media sobre los tokens de Lean): la dirección unitaria de la diferencia de medias entre adecuadas e inadecuadas (u), la coordenada media (g) y la mitad de la distancia entre las medias de clase (h).
- Controles: la misma construcción con las activaciones de `lean_only`, y 20 direcciones al azar por capa (semillas 2000 a 2019). Todos usan el mismo h.

## 3. Intervención

Una pasada limpia da, por fila y capa, la coordenada media m sobre los tokens de Lean. Después, en los embeddings y en la salida de cada bloque menos el último, se suma a todos los tokens de Lean el mismo múltiplo de la dirección, el necesario para que la coordenada media quede en un objetivo. La variación entre tokens no se toca y el objetivo se fija capa por capa, así que el desplazamiento no se acumula.

- **Desplazar:** objetivo m + f·s·h, con s = +1 en las filas inadecuadas y −1 en las adecuadas. Con f = 2 la fila recorre la distancia completa entre las medias de clase. Con f = 0 (placebo) los ganchos trabajan y el objetivo es la coordenada limpia.
- **Pareja:** objetivo m más la diferencia guardada entre la coordenada de su pareja y la suya.
- **Borrar:** objetivo g para todas las filas.

Son 54 condiciones por fila: base, placebo, desplazar con f = 2 (sonda, `lean_only` y 20 al azar), desplazar con f = 4 y f = 8 (sonda y 5 al azar cada una), pareja (sonda y 5 al azar) y borrar (sonda, `lean_only` y 10 al azar).

## 4. Medida principal y criterio

Medida: AUROC pareada de P(Yes) sobre los 377 pares, con intervalo por remuestreo de orígenes (2000 réplicas). La caída de una condición es la AUROC de base menos la suya.

**Criterio principal (f = 2).** Se cumple si las dos cosas ocurren a la vez:

1. el intervalo del 95 % de la caída con la dirección de la sonda menos la media de las caídas con las 20 direcciones al azar queda por encima de cero;
2. la caída con la dirección de la sonda es mayor que cada una de las 20 caídas al azar.

## 5. Secundarias, todas descriptivas

- Desplazamiento firmado del margen logit(Yes) − logit(No) respecto a la base, positivo cuando la respuesta se mueve hacia la clase contraria, frente a las mismas direcciones al azar.
- Dosis f = 4 y f = 8, pareja y borrar, cada una frente a sus direcciones al azar.
- Sonda frente a `lean_only` con f = 2.
- Comprobaciones sin etiquetas: placebo frente a base, base frente al P(Yes) guardado, coordenada limpia frente a la guardada.

## 6. Qué se dirá

- **Si el criterio se cumple:** «En Qwen3-4B, desplazar la media sobre los tokens de Lean hacia la clase contraria a lo largo de la diferencia de medias, en todas las capas, reduce la AUROC pareada de P(Yes) más que el mismo desplazamiento a lo largo de direcciones al azar (análisis exploratorio y post hoc, un solo modelo).»
- **Si no se cumple:** «No se establece que desplazar la media sobre los tokens de Lean a lo largo de la diferencia de medias cambie P(Yes) más que el mismo desplazamiento a lo largo de una dirección al azar.» Se informan las dosis tal como salgan.

En los dos casos se informan todos los números de las secciones 4 y 5.

## 7. Límites que se declaran desde ahora

- Un resultado nulo no muestra que el modelo no use esa información. Dice que su respuesta no depende de este eje de la media, y la intervención deja intacta la variación entre tokens, que puede llevar la misma información por otra vía.
- Un resultado positivo vale para un modelo, un conjunto de pares y una familia de direcciones. No convierte «es decodificable linealmente» en una afirmación sobre lo que el modelo calcula.
- El modelo corre en bfloat16. Cada intervención añade ruido de redondeo, que el placebo y las direcciones al azar comparten.
- h es pequeño frente a la variación entre ítems (unas 0,15 desviaciones típicas dentro de clase en la capa fija), de modo que f = 2, 4 y 8 quedan dentro del rango natural de la coordenada.

## 8. Lo que ya se conoce al escribir esta regla

El paso `direcciones` ya se ejecutó sobre las activaciones guardadas, sin pasar por el modelo. En la capa fija (24), la proyección sobre la diferencia de medias da una AUROC pareada de 0,879 fuera de partición, el coseno entre la dirección de la sonda y la de `lean_only` está entre 0,54 y 0,57, y la diferencia media entre las dos filas de un par vale 1,89 h a lo largo de la sonda frente a 0,11 h en valor absoluto a lo largo de una dirección al azar. No se ha visto ningún P(Yes) bajo esta intervención. El guion se probó de punta a punta solo con un modelo de juguete en CPU.

## 9. Lo que no se hará

No se cambian f, las capas, las direcciones, el número de controles ni el criterio después de ver los resultados. Cualquier análisis añadido se rotula como posterior a esta regla.

## 10. Aprobación

La corrida completa y el análisis exigen `probes/intervencion/APROBADO_regla_S5`, creada por Carlos, con el SHA-256 de este archivo.
