# Enmienda 1 al protocolo confirmatorio v1 (firmada): fuente inmediata, residuo de la copia e instantánea por conteo

**Estado:** borrador del 23 nov 2026, escrito por Claude Code tras las decisiones de Carlos de ese día: «Sí, la T por conteo», «No importa. Nos sirven», «Pero no detengas la via del conteo», «tomemos las limpias», «Inclúyelas» y «Lo quiero todo».

**Firmada por Carlos Orrego-Franco el 23 nov 2026**, partes A, B y C, con la respuesta «Firmo A, B y C» a la pregunta que citaba el SHA-256 del borrador (`ec7aae964d510bef650994103d52e2f3a8cd89588d42308377cc71b3638fb92d`). Este texto es ese borrador con solo esta cabecera cambiada. Enmienda `faithfulness/protocolo_confirmatorio_v1.md` (SHA-256 `4ed610f834806a660efb183481b1ad40cb53117d2c072937c811a249d90135db`), que no se edita. Se firma como v1: SHA-256, hora en `probes/BITACORA.md` y copia en `faithfulness/`. Las tres partes se pueden firmar por separado.

**Qué se ha visto de los datos.** Se escribe antes de generar o certificar ninguna infiel de las fuentes nuevas y antes de extraer ninguna activación. De ellas solo se conocen conteos y una muestra de NL y Lean revisada a la vista para comprobar la extracción. No se calculó ninguna métrica con etiquetas.

---

## Parte C. Fuente principal inmediata: el núcleo limpio del corpus de fieles

**Añade** al párrafo «Datos» de v1:

> Además de los enunciados posteriores al 23 oct 2026, entra como fuente el núcleo limpio del corpus de fieles del 23 nov 2026. Es `datos/fieles/limpias_qwen3_4b.jsonl` (SHA-256 en la bitácora de ese día; regla en `probes/fieles/limpias.py`): formalizaciones de nivel a cuyo Lean se hizo público después del 2025-07-26, con el campo `estrato` (`principal`, `margen_corto`).

**Exclusiones, las del escenario E3 aplicadas a esta fuente:**
- todo origen de formal-conjectures que esté entre los 270 del piloto, los 583, los 590 de `v3_previo`, las tripletas, los elegibles de tripletas o los documentos de revisión del piloto;
- todo origen de un archivo con algún origen de los 270.

**Lo que queda (conteo del 23 nov, solo fieles):** 3698 de formal-conjectures, 1141 de otras fuentes del estrato principal (IndiMathBench, formal-imo, ArXivLean, FATE-H, FATE-X, LeanCat, formal-putnam-like, Compfiles, PutnamBench 2025) y 19 925 del estrato `margen_corto` (NuminaMath-LEAN humano). En total, **24 764 fieles**.

**Instrumento:**
- Primero se elabora cada enunciado en el entorno de certificación congelado (Lean 4.34.1 + Mathlib del proyecto); los que no elaboren salen.
- Las infieles se generan con el generador v3 (v3.1 solo con un adaptador de entrada para estas fuentes, que reproduzca `candidatos_v3.jsonl` byte a byte con las entradas viejas) y se certifican con el certificador del piloto.
- Generador, adaptador y certificador se congelan por SHA antes de generar ninguna infiel.

**Estratos en el análisis:**
- La hipótesis de v1 se evalúa sobre la unión, con la fuente y el estrato como estratos del bootstrap.
- Se reporta además, como descriptivo, la diferencia en el estrato `principal` solo y en `margen_corto` solo.
- `margen_corto` cumple la regla de fechas por 5 días frente a Qwen3-4B. Si algún día se sondea un modelo posterior al 2025-07-31, ese estrato se excluye para ese modelo.

**Suministro esperado.** Con el rendimiento del piloto (2,65 % de orígenes con par por declaración en formal-conjectures y del orden del 8 % en competición), esta fuente daría del orden de 100 orígenes de formal-conjectures, de 60 a 90 de las demás fuentes principales y de 1500 a 1700 de NuminaMath-LEAN. Es una extrapolación, no una medición.

**Lo que cambia en la redacción final:**
- el NL de las competiciones antiguas es anterior a los modelos, así que la fuente es «limpia en el lado Lean, no en el NL», igual que formal-conjectures en v1;
- la mezcla de fuentes es otra que la del piloto (mucha competición), y el informe lo dice.

---

## Parte A. Instantánea por conteo

**Sustituye**, en el párrafo «Instantánea» de v1, solo la frase de la fecha.

**Texto nuevo.**
- El análisis confirmatorio se hace cuando el conteo de §A.2 llegue a **N = 400** orígenes con algún par A, B o C3 certificado, sumando las fuentes de la Parte C, de la Parte B (si se firma) y de los enunciados de formal-conjectures posteriores al 23 oct 2026.
- El conteo se hace el día 1 de cada mes, empezando el primer día 1 después de congelar el instrumento de la Parte C. Si no llega, la instantánea de formal-conjectures es el 1 nov 2027, 00:00 UTC.
- La prórroga única hasta el 1 feb 2028 si hay menos de 200 orígenes no cambia.
- **N = 400 es la recomendación;** Carlos puede fijar otro valor antes de firmar. Con la hipótesis de tres contrastes de v1, 400 orígenes dan un efecto mínimo detectable de 0,077 (ρ = 1) a 0,090 (ρ = 0).

### A.2 El conteo

- **Qué cuenta:** orígenes con al menos un par A, B o C3 certificado con el instrumento congelado. Se escribe solo el número de orígenes y de pares por familia y fuente, la fecha y los SHA. No se calcula ninguna métrica con etiquetas ni se extrae ninguna activación antes de llegar a N.
- **Por qué no altera nada:** `generar.emparejar` sortea con una semilla por origen, así que un conteo posterior no cambia los pares ya contados. La decisión de cuándo analizar depende solo del número de pares.

---

## Parte B. El residuo de la copia como estrato aparte

**Añade** al párrafo «Datos» de v1:

> Un estrato con los orígenes de la copia `c094b979` que el piloto no emparejó: las infieles compuestas A, B y C3 de `poblacion_candidata_2026-11-23.jsonl` (`ac5cf891…`) en el escenario E3 (140 orígenes como máximo), decididas por el certificador ampliado según las reglas aprobadas (opciones 1 y 2a: 1 de 20 el 23 nov; opción 3: `regla_opcion3_BORRADOR.md`). Su fiel D ya está certificada. Entran solo los ítems con fecha pública posterior a la de cada modelo.

Es otra clase de enunciados (grafos, conjuntos, polinomios, cardinales, enunciados cerrados), seleccionados por ser certificables, y el informe lo declara. Ningún origen suyo se analizó, pero pasaron por la certificación del piloto.
