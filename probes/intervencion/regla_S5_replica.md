# Regla de la réplica de S5 en Gemma-3, OLMo-2 y Llama-3.1 (Nivel B)

Fecha: 12 de noviembre de 2026. Guiones: `probes/intervencion/replica_s5.py`, que envuelve `probes/intervencion/intercambio.py` sin modificarlo. Borrador para aprobación de Carlos Orrego-Franco.

**Estatus.** Esta regla se escribe después de ver el resultado de S5 en Qwen3-4B y antes de calcular nada de S5 en los otros tres modelos, tampoco sus direcciones. No forma parte del prerregistro del artículo. Es una prueba con el guion y el criterio fijados de antemano; cómo se nombra en el artículo lo decide Carlos. El resultado de Qwen3-4B sigue siendo exploratorio y post hoc.

## 1. Pregunta

En Qwen3-4B, desplazar la media sobre los tokens de Lean hacia la clase contraria a lo largo de la diferencia de medias redujo la AUROC pareada de P(Yes) más que el mismo desplazamiento a lo largo de direcciones al azar. ¿Ocurre lo mismo en Gemma-3 (`gemma3_4b`), OLMo-2 (`olmo2_7b`) y Llama-3.1 (`llama31_8b`)?

## 2. Qué se mantiene idéntico

Todo lo que fija `regla_S5.md` (SHA-256 3e9ca659…) en sus secciones 2 a 5:

- los 377 pares certificados del Nivel B (754 filas, 256 orígenes), el prompt `full` con la pregunta y la lectura de P(Yes) tras «**Answer:»;
- las cinco particiones por archivo fuente (semilla 0), con direcciones estimadas fuera de partición;
- la intervención sobre la media de los tokens de Lean, en los embeddings y en la salida de cada bloque menos el último;
- las 54 condiciones, con las mismas semillas para las direcciones al azar (2000 a 2019);
- la medida (AUROC pareada de P(Yes), remuestreo de orígenes con 2000 réplicas) y las secundarias.

El guion es `intercambio.py` tal como corrió la noche del 11 de noviembre (SHA-256 8c948cd8…). Cada modelo usa sus propias activaciones guardadas, sus propias direcciones y su propio h.

## 3. Criterio, por modelo

El mismo de S5, con f = 2. Un modelo cumple si las dos cosas ocurren a la vez:

1. el intervalo del 95 % de la caída con la dirección de la sonda menos la media de las caídas con las 20 direcciones al azar queda por encima de cero;
2. la caída con la dirección de la sonda es mayor que cada una de las 20 caídas al azar.

No hay ajuste por modelo: ni f, ni capas, ni número de controles.

## 4. Comprobaciones previas, por modelo

El humo (4 pares, 9 condiciones) debe pasar antes de la corrida completa. Si no pasa, el modelo no se corre y se informa como no evaluado.

- Ganchos: queda menos del 10 % de la distancia al objetivo (lo exige `intercambio.py`).
- La coordenada limpia reproduce la guardada: mediana de la diferencia en la capa fija de 0,05 h como máximo.
- El P(Yes) de base reproduce el guardado: diferencia máxima de 0,2 como máximo.

## 5. Qué se dirá

«Con el mismo guion y el mismo criterio, fijados antes de correr, el resultado de S5 en Qwen3-4B se repite en k de los n modelos evaluados (nombres).» Se dice con el k que salga, también si es cero. Para cada modelo se informan todos los números de las secciones 4 y 5 de `regla_S5.md`, cumpla o no.

Un modelo que no termine por un fallo técnico se informa como no evaluado. No cuenta como réplica fallida ni como réplica lograda.

## 6. Lo que ya se conoce al escribir esta regla

- S5 en Qwen3-4B: AUROC de base 0,838; con f = 2, 0,689; caída menos media al azar 0,145 [0,112; 0,177]; mayor que las 20 al azar.
- S3 en los tres modelos: la etiqueta es decodificable linealmente de la media sobre los tokens de Lean por encima de los controles de superficie y del P(Yes) propio.
- AUROC pareada de P(Yes) sin intervenir: OLMo-2 0,726 [0,679; 0,771], Llama-3.1 0,729 [0,688; 0,771], Gemma-3 0,560 [0,512; 0,605].
- No se ha calculado ninguna dirección ni ningún P(Yes) bajo intervención en estos tres modelos. El guion no se ha ejecutado con ellos; se comprobó solo que sus clases aceptan las mismas llamadas, con modelos de juguete.

## 7. Límites que se declaran desde ahora

- En Gemma-3 el P(Yes) de base separa poco. El criterio es el mismo, porque la intervención puede llevar la AUROC por debajo de 0,5, pero un incumplimiento ahí se lee con esa salvedad.
- Los de la sección 7 de `regla_S5.md` siguen valiendo: un nulo no muestra que el modelo no use la información, un positivo no dice qué calcula el modelo, y bfloat16 añade ruido que los controles comparten.
- Tres modelos, un conjunto de pares, una familia de direcciones.

## 8. Lo que no se hará

No se cambian el criterio, las condiciones ni los umbrales después de ver resultados. Si `intercambio.py` necesita un arreglo de compatibilidad para cargar o llamar a un modelo, se admite solo si no altera la intervención ni el análisis, y se anota con el SHA-256 nuevo. Cualquier análisis añadido se rotula como posterior a esta regla.

## 9. Aprobación

Todos los pasos, incluidos `direcciones` y el humo, exigen `probes/intervencion/APROBADO_regla_S5_replica`, creada por Carlos, con el SHA-256 de este archivo.
