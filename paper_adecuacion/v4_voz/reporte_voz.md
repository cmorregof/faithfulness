# Reporte de voz: «Beyond the Lean Alone», v3 → v4

11 de noviembre de 2026. Entrada: `v3_tmlr/main_en.tex` y `v3_tmlr/main_es_v3.tex`. Salida: `v4_voz/main_en.tex` y
`v4_voz/main_es.tex`, con sus PDF. No se tocó nada de `v3_tmlr/`.

## Qué cambió y qué no

Solo cambió la prosa. El preámbulo, las nueve tablas, las cuatro figuras con sus leyendas, las ecuaciones, las
etiquetas y las citas se copiaron byte a byte del original con un script, sin volver a teclearlas. Los nombres de
condición, de lectura, de nivel y de familia quedaron como estaban. Los títulos de sección y de párrafo tampoco
cambiaron.

El español se reescribió a partir de `main_es_v3.tex`, no del inglés nuevo. Las decisiones de contenido (qué sale
del resumen, qué frase cambia de párrafo) son las mismas en los dos idiomas, para que digan lo mismo.

| | Inglés v3 | Inglés v4 | Español v3 | Español v4 |
|---|---|---|---|---|
| Resumen (palabras) | 406 | 237 | 453 | 246 |
| Números en el resumen | 19 | 7 | 19 | 7 |
| Punto y coma en la prosa | 28 | 0 | 28 | 0 |
| Dos puntos en la prosa | 28 | 3 | 28 | 5 |
| Palabras por frase (media aproximada) | 29 | 22 | 33 | 25 |
| Páginas | 17 | 17 | 17 | 18 |

Los dos puntos que quedan son los de tres títulos de sección y, en español, los de las dos listas de modelos.
El español pasa a 18 páginas porque los párrafos largos se partieron; la página 18 tiene un tercio de texto.

Las tres cifras del resumen son 450, 377 y +0.045 con su intervalo [0.021, 0.069]. Los otros números que cuenta el
script son el 4 de «Lean 4» y el 95 del intervalo.

## Inglés: los cinco cambios principales

**1. Resumen.** De 406 a 237 palabras y de once cifras a tres.

- Antes: «(A) On 450 CriticLeanBench formalizations with human-validated labels, none of the four models of a
  preregistered replication met the per-model criterion, so the global criterion failed as well. A post hoc bootstrap
  that resamples the same items jointly for the four models puts their mean gap at +0.045 (95% CI [0.021, 0.069])
  under the readout at a layer fixed in advance, and at +0.029 [−0.000, 0.058] under the last-token readout.»
- Después: «On 450 CriticLeanBench formalizations a preregistered replication did not pass, because none of its four
  models met the per-model criterion. A post hoc bootstrap puts their mean gap at +0.045 (95% CI [0.021, 0.069]) at a
  fixed layer, whereas at the last token the interval includes zero.»

**2. La regla del prerregistro (Level A, Preregistration).** Una frase con dos condiciones y un inciso dentro de la
primera pasó a ser cuatro frases, y el párrafo se partió en tres: la regla, las dos cláusulas confirmadas tarde y la
diferencia entre permutación y bootstrap.

- Antes: «A model passes if, in either readout, (a) its p-value from 1000 permutations, each of which shuffles the
  labels, refits both probes and recomputes Δ, is below 0.05 after Holm correction over the eight tests (four models,
  two readouts), and (b) the interval of full minus stacked lies entirely above zero.»
- Después: «Under its rule, a model passes if two conditions hold in either readout. Condition (a) is that its
  p-value from 1000 permutations is below 0.05 after Holm correction over the eight tests (four models, two readouts).
  Each permutation shuffles the labels, refits both probes and recomputes Δ. Condition (b) is that the interval of
  full minus stacked lies entirely above zero.»

**3. La fuente del problema (Level A, Source of the problem).** Un bloque de unas 220 palabras quedó en tres
párrafos: la pregunta, la comparación dentro de la fuente y la prueba con una fuente apartada.

- Antes: «When faithful and unfaithful formalizations are compared only within the same source, and the comparison is
  pooled over sources, the mean gap of the four preregistered models under readout (ii) is +0.049 [0.021, 0.079].»
- Después: «The first check compares faithful and unfaithful formalizations only within the same source and pools the
  comparison over sources. The mean gap of the four preregistered models under readout (ii) is then +0.049
  [0.021, 0.079].» El párrafo siguiente abre con «The second check trains the probe on eleven sources and tests it on
  the twelfth.»

**4. Los mapas (Level A, Where the separation is readable).** Salió el paréntesis con punto y coma, y el párrafo de
las diferencias abre diciendo de qué trata.

- Antes: «In the five general-purpose models this direction, fitted on Lean tokens, is at or near chance over the
  statement span (0.49 to 0.52 on average; the one exception is Qwen3-8B, at 0.521 [0.501, 0.543]), where the model
  has not yet read the Lean, and rises over the Lean tokens in the upper layers.»
- Después: «In the five general-purpose models this direction, fitted on Lean tokens, is at or near chance over the
  statement span, where the model has not yet read the Lean. On average it lies between 0.49 and 0.52 there, and the
  one exception is Qwen3-8B, at 0.521 [0.501, 0.543]. It then rises over the Lean tokens in the upper layers.»

**5. Los controles del Nivel B (What the controls say y The second readout).** Dos frases sobre controles en el
último token estaban al comienzo del párrafo de la segunda lectura. Pasaron al párrafo de los controles, y el de la
segunda lectura abre ahora con lo que le corresponde.

- Antes, al abrir «The second readout»: «On the numeral edits examined below the cross-surface features reach 0.933,
  which the n-grams do not. At the last token, no model exceeds both the n-gram control and its own P(Yes) with
  intervals above zero. Every control at Level B was computed against the last-token probe only; none was computed
  for the second readout.»
- Después, al abrir «The second readout»: «Every control at Level B was computed against the last-token probe only,
  and none was computed for the second readout. The gap over the Lean alone was measured at both, and it also
  depends on the readout.»

## Español: los cinco cambios principales

**1. Resumen.** De 453 a 246 palabras y de once cifras a tres.

- Antes: «(B) En 377 pares mínimos cuya no equivalencia certifica Lean, las corridas exploratorias dieron una brecha
  positiva sobre el Lean solo en tres de cuatro modelos en el último token y en los cuatro en la media sobre los
  tokens de Lean. Frente al más fuerte de dos controles de superficie, los n-gramas simples de ambos textos, solo un
  modelo conserva, en el último token, un margen cuyo intervalo excluye el cero.»
- Después: «En 377 pares mínimos certificados por Lean, corridas exploratorias dieron una brecha positiva en tres de
  cuatro modelos en el último token, pero frente al control de superficie más fuerte solo uno conserva un margen cuyo
  intervalo excluye el cero.»

**2. La construcción de los pares (Nivel B, Construcción).** El párrafo de unas 260 palabras quedó en cuatro: qué es
un par, las familias, de dónde sale el lote y lo que pide la regla.

- Antes: «Cada par reúne dos ediciones mínimas del mismo enunciado original en Lean: una que Lean certifica como
  equivalente al original (el miembro adecuado) y otra que Lean certifica como no equivalente (el miembro
  inadecuado).»
- Después: «Cada par reúne dos ediciones mínimas del mismo enunciado original en Lean. Lean certifica una de ellas
  como equivalente al original, y esa edición es el miembro adecuado. Certifica la otra como no equivalente, y esa es
  el miembro inadecuado.»

**3. El metaanálisis (Nivel A).** La razón va ahora antes que el remedio, y el paréntesis pasó a la frase.

- Antes: «Los cuatro modelos se puntuaron sobre las mismas 450 formalizaciones, así que sus estimaciones no son
  independientes y el intervalo de efectos aleatorios es demasiado estrecho. Un bootstrap post hoc que remuestrea los
  mismos grupos conjuntamente para los cuatro modelos (2000 remuestreos, estratificados por clase) sitúa su brecha
  media en +0.045 [0.021, 0.069] con (ii) y en +0.029 [−0.000, 0.058] con (i).»
- Después: «El intervalo de efectos aleatorios es demasiado estrecho, porque los cuatro modelos se puntuaron sobre
  las mismas 450 formalizaciones y sus estimaciones no son independientes. Un bootstrap post hoc atiende ese problema
  al remuestrear los mismos grupos conjuntamente para los cuatro modelos, con 2000 remuestreos estratificados por
  clase. Sitúa su brecha media en +0.045 [0.021, 0.069] con (ii) y en +0.029 [−0.000, 0.058] con (i).»

**4. Las ediciones de numeral (Nivel B, familia C).** Salieron los dos puntos que hacían de «porque».

- Antes: «En C2 el control de superficie cruzada alcanza 0.933 por sí solo, indistinguible de las activaciones
  (0.913; diferencia −0.020 [−0.103, 0.056]): en el 84% de esos pares el miembro inadecuado tiene más numerales de
  Lean ausentes del enunciado que el adecuado, y un rasgo que los cuenta no necesita modelo alguno.»
- Después: «En C2 el control de superficie cruzada alcanza 0.933 por sí solo, lo que es indistinguible de las
  activaciones, que dan 0.913 (diferencia −0.020 [−0.103, 0.056]). Ocurre así porque en el 84% de esos pares el
  miembro inadecuado tiene más numerales de Lean ausentes del enunciado que el adecuado, y un rasgo que los cuenta no
  necesita modelo alguno.»

**5. La conclusión.** Un solo párrafo quedó en dos: lo que el piloto sostiene y lo que queda por hacer. La frase de
los intervalos perdió los dos puntos.

- Antes: «Varios de sus intervalos incluyen el cero: la mayoría de los de la lectura en el último token en el
  Nivel A, donde Llama-3.1 es negativo, y Gemma-3 en el último token en el Nivel B.»
- Después: «Varios de sus intervalos, sin embargo, incluyen el cero. Son la mayoría de los de la lectura en el último
  token en el Nivel A, donde Llama-3.1 es negativo, y el de Gemma-3 en el último token en el Nivel B.»

## Frases donde no estoy seguro de haber conservado el sentido exacto

Valen para los dos idiomas. En cada una digo qué añadí o moví, para que decidas.

1. **Lo que salió del resumen, además de las cifras.** Salieron las dos comprobaciones por fuente, la segunda
   lectura del Nivel B («in all four at the mean over Lean tokens»), el nombre del control más fuerte («plain n-grams
   of both texts»), «in four of five models it is weaker there when the statement is removed», «report each result
   under the rule fixed for it» y «the single reference implementation that produced them». Todo sigue en el cuerpo.
   Si alguna te parece una salvedad esencial, vuelve al resumen: el inglés tiene 13 palabras de margen y el español 4.
2. **«under the last-token readout the interval includes zero».** El resumen ya no da +0.029 [−0.000, 0.058]; dice
   que el intervalo incluye el cero. El límite inferior es −0.000, así que lo incluye por muy poco; es una
   lectura de la cifra y no la cifra.
3. **«A post hoc bootstrap addresses this by resampling…» / «Un bootstrap post hoc atiende ese problema al
   remuestrear…».** El original ponía una frase al lado de la otra. Yo escribí que el bootstrap conjunto responde a
   la falta de independencia. Creo que es lo que quieres decir, pero el original no lo afirmaba.
4. **«As a result, the source alone separates the labels…» / «En consecuencia, la fuente sola separa…».** Añadí el
   conector causal entre «la proporción difiere de una fuente a otra» y «la fuente separa las etiquetas».
5. **«Over the Lean tokens, the separation is weaker in four of the five models when the statement is removed.»**
   Esa afirmación estaba solo en el resumen viejo. Ahora abre el párrafo de las diferencias por región, porque el
   párrafo necesitaba decir de qué trata. La salvedad de OLMo-2 sigue cinco frases más abajo, y «The maps are
   exploratory» cierra el párrafo como antes.
6. **Dos frases cambiaron de párrafo en el Nivel B** (cambio 5 del inglés). No cambia lo que dicen, pero «At the last
   token, no model exceeds both the n-gram control and its own P(Yes)» queda ahora justo después de la frase sobre
   P(Yes) en Qwen3-4B, y puede leerse como su consecuencia.
7. **«The gap over the Lean alone was measured at both, and it also depends on the readout.» / «La brecha sobre el
   Lean solo sí se midió en ambas…».** Añadí «was measured at both» para preparar el cambio de tema. Lo sostiene la
   Tabla 3, que trae las dos lecturas.
8. **«Under the same rule, a model whose interval for Δ includes zero is recorded as a null…» / «Por la misma
   regla…».** El original no decía de dónde sale esa convención. La atribuí a la regla porque la leyenda de la Tabla 3
   dice «By the rule […] the fourth is a null with upper bound 0.107».
9. **«For comparison, on all 408 the gap in Qwen3-4B is +0.213…» / «Como referencia, con los 408…».** Añadí dos
   palabras para que la cifra no quedara suelta. No digo qué se concluye de ella, igual que el original.
10. **«Ill-typed candidates are therefore among its negatives» / «Entre sus negativos hay, por tanto…».** Añadí el
    conector.
11. **Frases de apertura nuevas.** Resumen lo que el párrafo ya decía, pero son frases que no existían: «We look
    inside instead» (Introducción), «The work that measures faithfulness from the outside also supplies two of our
    benchmarks», «Decoding correctness from hidden states has precedent», «The effect was first seen in a single
    model», «Two null controls check whether the architecture alone, or a generic encoder, would produce the gap»,
    «Qwen3-8B was added later and is exploratory», «The model's own answer sets a further limit», «Part of the data
    was public before some of the models were released», «The labels have a different weakness at each level» y
    «Several analyses were decided after seeing results». El español tiene las equivalentes.
12. **«exploratory» aparece una vez más en el cuerpo** (12 en lugar de 11), por la frase sobre Qwen3-8B del punto
    anterior. El párrafo ya se titulaba «A later exploratory model».
13. **Dos cosas que vi y no toqué**, porque son de contenido. (a) En «Decision», «Under readout (i) only
    DeepSeek-Prover-V2 meets condition (b), with p = 0.084» no dice de qué prueba es ese p; lo dejé igual. (b) En
    «Construction» el texto dice primero que el lote tiene 377 pares «after exclusions fixed before any activation
    was extracted» y después que Lean certificó 408 y se retiraron 31. Leído en orden cuesta ver que son las mismas
    exclusiones. No lo reordené porque sería afirmar que lo son.

## Verificación

El script es `verifica_voz.py` (está en esta carpeta). Compara la versión vieja y la nueva de cada idioma. Los
números se toman con signo y decimales, y se cuentan también los que van dentro de nombres (el 3 y el 4 de
«Qwen3-4B», el 4 de «Lean 4»), así que el número de menciones de cada modelo tampoco cambió.

Cuatro extremos de intervalo que salieron del resumen (0.090, 0.121, 0.165 y 0.187, del Nivel C) están en el cuerpo
solo en la Tabla 6, donde llevan el signo + explícito. El script lo marca aparte. El 0.090 aparece además sin signo
en otro intervalo del Nivel B.

### Inglés

```
VIEJO: v3_tmlr/main_en.tex
NUEVO: v4_voz/main_en.tex

== 1. Números fuera del resumen ==
[OK] multiconjunto de números  (viejo: 921, nuevo: 921)

== 2. Claves ==
[OK] \cite*  (viejo: 40, nuevo: 40)
[OK] \ref  (viejo: 18, nuevo: 18)
[OK] \label  (viejo: 15, nuevo: 15)
[OK] \includegraphics  (viejo: 4, nuevo: 4)

== 3. Matemática, tablas y figuras ==
[OK] matemática en línea y en bloque  (viejo: 23, nuevo: 23)
[OK] entornos table  (viejo: 9, nuevo: 9)
[OK] entornos figure  (viejo: 4, nuevo: 4)

== 4. Números que salieron del resumen ==
      −0.000  en el cuerpo (4 veces)
       0.021  en el cuerpo (4 veces)
      +0.029  en el cuerpo (3 veces)
      +0.049  en el cuerpo (2 veces)
       0.058  en el cuerpo (3 veces)
       0.079  en el cuerpo (2 veces)
       0.090  en el cuerpo (1 veces)
       0.121  en el cuerpo como +0.121 (extremo de intervalo con signo explícito en tabla)
      +0.127  en el cuerpo (1 veces)
      +0.154  en el cuerpo (1 veces)
       0.165  en el cuerpo como +0.165 (extremo de intervalo con signo explícito en tabla)
       0.187  en el cuerpo como +0.187 (extremo de intervalo con signo explícito en tabla)
    resumen viejo: 406 palabras, 19 números; nuevo: 237 palabras, 7 números -> ['+0.045', '0.021', '0.069', '377', '4', '450', '95']

== Informativo ==
    «exploratory»: resumen 3 -> 3, cuerpo 11 -> 12   <-- cambió en el cuerpo
    «post hoc»: resumen 2 -> 1, cuerpo 9 -> 9
    «not a replication»: resumen 0 -> 0, cuerpo 1 -> 1
    «No level alone supports»: resumen 1 -> 1, cuerpo 1 -> 1
    «preliminary»: resumen 1 -> 1, cuerpo 1 -> 1
    nombres protegidos (?:Level|Levels|Nivel|Niveles)~[ABC]: solo viejo {}, solo nuevo {'Level~A': 2, 'Level~B': 1, 'Level~C': 1}
    giros prohibidos en la prosa nueva: ninguno

RESULTADO: TODO IDÉNTICO
```

### Español

```
VIEJO: v3_tmlr/main_es_v3.tex
NUEVO: v4_voz/main_es.tex

== 1. Números fuera del resumen ==
[OK] multiconjunto de números  (viejo: 921, nuevo: 921)

== 2. Claves ==
[OK] \cite*  (viejo: 40, nuevo: 40)
[OK] \ref  (viejo: 18, nuevo: 18)
[OK] \label  (viejo: 15, nuevo: 15)
[OK] \includegraphics  (viejo: 4, nuevo: 4)

== 3. Matemática, tablas y figuras ==
[OK] matemática en línea y en bloque  (viejo: 23, nuevo: 23)
[OK] entornos table  (viejo: 9, nuevo: 9)
[OK] entornos figure  (viejo: 4, nuevo: 4)

== 4. Números que salieron del resumen ==
      −0.000  en el cuerpo (4 veces)
       0.021  en el cuerpo (4 veces)
      +0.029  en el cuerpo (3 veces)
      +0.049  en el cuerpo (2 veces)
       0.058  en el cuerpo (3 veces)
       0.079  en el cuerpo (2 veces)
       0.090  en el cuerpo (1 veces)
       0.121  en el cuerpo como +0.121 (extremo de intervalo con signo explícito en tabla)
      +0.127  en el cuerpo (1 veces)
      +0.154  en el cuerpo (1 veces)
       0.165  en el cuerpo como +0.165 (extremo de intervalo con signo explícito en tabla)
       0.187  en el cuerpo como +0.187 (extremo de intervalo con signo explícito en tabla)
    resumen viejo: 453 palabras, 19 números; nuevo: 246 palabras, 7 números -> ['+0.045', '0.021', '0.069', '377', '4', '450', '95']

== Informativo ==
    «post hoc»: resumen 2 -> 1, cuerpo 9 -> 9
    «exploratori»: resumen 3 -> 3, cuerpo 11 -> 12   <-- cambió en el cuerpo
    «no es una réplica»: resumen 0 -> 0, cuerpo 1 -> 1
    «Ningún nivel sostiene por sí solo»: resumen 1 -> 1, cuerpo 1 -> 1
    «preliminares»: resumen 1 -> 1, cuerpo 1 -> 1
    nombres protegidos (?:Level|Levels|Nivel|Niveles)~[ABC]: solo viejo {}, solo nuevo {'Nivel~A': 2, 'Nivel~B': 1, 'Nivel~C': 1}
    nombres protegidos (?:famil(?:y|ies|ia|ias)) [ABC]\b: solo viejo {}, solo nuevo {'familia A': 1}
    giros prohibidos en la prosa nueva: ninguno

RESULTADO: TODO IDÉNTICO
```

Las tres líneas del bloque «Informativo» que no son cero se explican así. «post hoc» baja de 2 a 1 en el resumen
porque salió la frase de las comprobaciones por fuente; en el cuerpo sigue 9 veces. «exploratory» sube de 11 a 12 en
el cuerpo por la frase sobre Qwen3-8B. «Level A», «Level B» y «Level C» aparecen cuatro veces más porque la primera
contribución nombra ahora los niveles en lugar de poner (A), (B) y (C), y porque el párrafo de datos abre con
«Level A uses…».

## Las dos versiones dicen lo mismo

Lo comprobé de dos maneras. La primera es `coteja_en_es.py`, que parte cada versión en bloques de prosa y compara,
bloque a bloque y en orden, los números, las citas y referencias, las condiciones `\vr{...}`, las lecturas y los
nombres de modelos y familias.

```
bloques de prosa: EN 102, ES 102

RESULTADO: las secuencias coinciden en todos los bloques
```

La segunda fue leer los dos textos en paralelo. Las diferencias que quedan son de redacción. Las anoto por si
alguna te importa:

- Resumen: el inglés dice «the stronger of two surface controls» y el español «el control de superficie más fuerte»;
  el inglés dice «written after the models' release and after this pilot» y el español «posteriores a los modelos y a
  este piloto». El español no tenía palabras para más.
- Modelos: el inglés introduce las dos listas con «namely» y el español con dos puntos.
- El español conserva la aclaración «(\emph{faithfulness})» en la Introducción y la nota de términos propia, como
  en la v3.

## Compilación

`latexmk -pdf main_en.tex` y `latexmk -pdf main_es.tex`, con pdfTeX (TeX Live), sin errores, sin cajas
desbordadas, sin referencias ni citas sin resolver y sin avisos de BibTeX. Los únicos avisos son los de
«`h' float specifier changed to `ht'», cinco por idioma; la v3 daba cinco en inglés y tres en español.

| | v3 | v4 |
|---|---|---|
| `main_en.pdf` | 17 páginas | 17 páginas |
| `main_es.pdf` | 17 páginas | 18 páginas |

Para que la carpeta compile sola copié en `v4_voz/` lo que los `.tex` necesitan y que no cambió: `refs.bib`,
`tmlr.sty`, `tmlr.bst`, `fancyhdr.sty` y los ocho PDF de `figuras_v3/`. Salen de `v3_tmlr/` y de
`paquete_v3.tgz`, sin modificar.

## Archivos de esta carpeta

- `main_en.tex`, `main_en.pdf`: inglés.
- `main_es.tex`, `main_es.pdf`: español.
- `reporte_voz.md`: este reporte.
- `verifica_voz.py`: `python3 verifica_voz.py ../v3_tmlr/main_en.tex main_en.tex` (y lo mismo con
  `../v3_tmlr/main_es_v3.tex main_es.tex`). Sale con código 1 si algo difiere.
- `coteja_en_es.py`: `python3 coteja_en_es.py main_en.tex main_es.tex`.
