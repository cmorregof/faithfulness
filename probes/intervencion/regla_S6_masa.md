# Regla de S6: masa de probabilidad en « Yes» y « No» bajo la intervención (Nivel B)

Fecha: 13 de noviembre de 2026. Guion: `probes/intervencion/masa_si_no.py`. Borrador para aprobación de Carlos Orrego-Franco.

**Estatus.** Esta regla se escribe después de ver todos los resultados de S5 (la AUROC de P(Yes) en los cuatro modelos) y antes de calcular nada sobre la masa. Nadie ha mirado la suma P(Yes) + P(No) de `pyes.npy`. El análisis es exploratorio y post hoc, y no forma parte del prerregistro del artículo. No corre ningún modelo: usa solo los `pyes.npy` que ya existen.

## 1. Pregunta

La intervención de S5 baja la AUROC pareada de P(Yes). Una explicación que no tiene que ver con el eje es que el desplazamiento dañe el modelo en general, de modo que deje de responder sí o no. Si eso pasara, la masa de probabilidad que el modelo pone en « Yes» y « No» caería más con la dirección de diferencia de medias que con direcciones al azar del mismo tamaño. S6 mide esa masa.

## 2. Datos

Los mismos de S5: los 377 pares certificados del Nivel B (754 filas, 256 orígenes) y, por modelo, `probes/intervencion/resultados_s5/<modelo>/pyes.npy`, con sus 54 condiciones. No se recalcula ni se modifica nada de S5.

## 3. Medida

Por fila y condición, M = P(« Yes») + P(« No») en la posición de la respuesta (las dos primeras columnas de `pyes.npy`). Por par se promedia M de sus dos miembros, luego se promedia dentro de cada origen y luego sobre orígenes, como en la AUROC pareada. Los intervalos del 95 % salen de 2000 remuestreos de orígenes con semilla 0, igual que en S5.

Se reporta, por modelo:

- M sin intervenir, con el placebo y con el desplazamiento principal (f = 2) a lo largo de la dirección de diferencia de medias;
- la media, el mínimo y el máximo de M sobre las 20 direcciones al azar con f = 2;
- D = M con la dirección de diferencia de medias menos la media de M sobre las 20 direcciones al azar, con su intervalo;
- cuántas de las 20 direcciones al azar dejan una masa igual o menor que la dirección de diferencia de medias.

Descriptivo, sin lectura: lo mismo con f = 4 y f = 8 (5 direcciones al azar cada una).

## 4. Lectura, por modelo, fijada antes de calcular

Con f = 2:

- **«pierde más masa que el azar»** si ocurren las dos cosas: el intervalo de D queda por completo por debajo de cero, y M con la dirección de diferencia de medias es menor que con cada una de las 20 direcciones al azar;
- **«no se establece que pierda más masa que el azar»** en cualquier otro caso.

No hay umbral sobre el valor absoluto de M. Se reporta tal cual.

## 5. Qué se hace con el resultado

Salga lo que salga, los cuatro modelos se reportan en el apéndice de resultados secundarios del artículo, como una columna más de esa tabla y una o dos frases. Si algún modelo «pierde más masa que el azar», el cuerpo lo dice en el párrafo de la intervención, junto al resultado de ese modelo.

## 6. Lo que S6 no muestra

Que la masa se conserve descarta un tipo de daño: que el modelo deje de responder sí o no. No descarta que la respuesta cambie por una vía distinta de la que se quería tocar, ni mide la fluidez del modelo fuera de esa posición. Si la masa cae, eso no anula S5, pero obliga a decir que la caída de la AUROC puede deberse en parte a daño general.

## 7. Aprobación

El guion solo calcula si existe `probes/intervencion/APROBADO_regla_S6` con el SHA-256 de este archivo. La marca la crea Carlos.
