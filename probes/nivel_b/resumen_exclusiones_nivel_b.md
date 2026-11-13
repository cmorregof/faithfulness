# Exclusiones del Nivel B: resumen de una página (5 nov 2026)

**Qué es:** la lista que fija `datos/exclusiones_nivel_b.json`.
- Se escribió el 5 nov a las 06:3x, antes de extraer ninguna activación del Nivel B.
- Se aplicó por la delegación de Carlos de esa noche, que él retiró después. Carlos la mantiene, y este resumen es para que la revise.
- Viene de `revision_confirmacion_certificados_opus.md` (Opus, esfuerzo xhigh), que revisó 15 pares certificados a mano y luego barrió los 408.
- Va atada a los SHA del parquet (`fb80e4b2…`), del índice y de los resultados de la certificación.

## Punto de partida
408 pares certificados en 270 orígenes:
- por familia de la infiel: A 168, B 139, C 101;
- por fuente: FormalMATH 69, formal_conjectures 339.

## Qué se excluyó y por qué

| Grupo | Pares | Orígenes | Composición | Motivo |
|---|---|---|---|---|
| **1. Obligatorio**: original FormalMATH no fiel al NL | 9 (pares 23, 24, 26, 27, 29, 36, 50, 51, 55) | 7: FM[212], [53], [287], [70], [274], [31], [210] | todos FormalMATH; A 4, B 3, C 2 | El Lean original no dice lo que dice el NL (detalle en la tabla siguiente). Si el original no es fiel, la «fiel» tampoco lo es y la etiqueta del par se invierte o pierde sentido. |
| **2. Fuera del principal; se reportan aparte**: «equivalentes de hecho» | 23 (17, 19, 23, 28, 34, 35, 38, 122, 147, 151, 215, 216, 297, 310, 312, 332, 333, 338, 350, 352, 367, 401, 402) | 22 | todos de familia A (A3∘D8 9, A1∘D4h 8, A3∘D1 5, A3∘D1c 1); FormalMATH 7, formal_conjectures 16 | La infiel solo añade un caso donde la conclusión es trivialmente verdadera; por ejemplo, k = 0 da una congruencia módulo 1. Lean certifica que las fórmulas no son equivalentes, pero no miró la conclusión en esos puntos nuevos. En contenido, la infiel dice lo mismo que el original: es ruido de etiqueta que empuja hacia el nulo. |
| **3. Solo sensibilidad** (siguen en el principal) | 4 (pares 4, 45, 56, 203) y las B3 de «caso base trivial» (~10, por identificar antes del análisis) | 4 | B 3, A 1 | FM[136], FM[385] y FM[73] son originales dudosos; el par 203 (Erdős 650) es de tipo ≤/<. Las B3 son el espejo del grupo 2: solo quitan un caso trivial. |

El par 23 está en los grupos 1 y 2. Por eso 408 − 9 − 23 + 1 = **377 pares en 256 orígenes** para el principal:
- por familia de la infiel: A 142, B 136, C 99;
- por fuente: FormalMATH 54, formal_conjectures 323.

### Detalle del grupo 1

| Origen | Problema |
|---|---|
| FM[212] | «Solve the inequality» formalizado como «para todo x», que es falso |
| FM[53] | Falta «other», y eso hace falso el original |
| FM[287] | División de ℕ |
| FM[70] | División total |
| FM[274] | El `∏` se calcula en ℕ y da 0; es muy probable, pero falta comprobarlo con un `#check` |
| FM[31] | Tautología |
| FM[210] | Original no fiel |

## Qué cambiaría si no se excluyera

**Solo sin el grupo 1:** 385 pares en 262 orígenes, todos con originales FormalMATH.
- El caso más grave es el 24: la «fiel» es falsa y la «infiel» verdadera.
- Esos pares entran con la etiqueta potencialmente invertida.
- El sesgo va en cualquier dirección y no se puede corregir después.

**Solo sin el grupo 2:** 399 pares en 263 orígenes, y la familia A pasa de 142 a 164.
- Son 23 pares de unos 400 (~6 %) donde ninguna lectura del contenido distingue fiel de infiel.
- Esperable: menos separación, hacia el nulo, y concentrada en la familia A.
- No crea falsos positivos, solo diluye.
- Por eso se reportan aparte y no se borran: el análisis con ellos es el contraste natural.

**Sin el grupo 3 (sensibilidad):** el principal no cambia. Solo se añade una fila de sensibilidad.

**Umbrales:** con o sin exclusiones se cumple el mínimo de 200 pares. Los 300 orígenes no se alcanzan en ningún caso (256–270), así que la rama es «potencia reducida» de todos modos.

## Lo que esto no resuelve

**Compuerta de superficie sobre los certificados:** 0,706, con exceso 0,081. No pasa, y Carlos la dejó como exploratoria.

**`verdad_variante`:** hay que corregirla antes del control de fidelidad ≠ verdad:
- 7 pares de nivel 1 tienen la variante falsa;
- las 4 B4∘D4c son verdaderas si el original lo es.

**Para futuras certificaciones:** falta un chequeo «accidental por la conclusión». Habría atrapado sin juicio humano unos 10 de los 23 del grupo 2.

**La regla de análisis** (tripletas) y la muestra de 30 esperan la firma de Carlos. Sin eso no se extraen activaciones.
