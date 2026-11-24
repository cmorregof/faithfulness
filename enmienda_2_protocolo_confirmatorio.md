# Enmienda 2 al protocolo confirmatorio v1 (firmada): corte en 500 orígenes, selección por orden de hash y tope por fuente

**Estado:** borrador del 24 nov 2026, escrito por Claude Code a partir del encargo de Carlos de ese día (puntos 2, 3 y 5, y la nota sobre los puntajes por fila).

**Firmada por Carlos Orrego-Franco el 24 nov 2026** con «Firmo la enmienda 2», respuesta a la pregunta que citaba el SHA-256 del borrador (`108c446caf6d1505899928bbc64a315af85f4ac7362c56dbeb2f4ebc4aa25665`). Este texto es ese borrador con solo la cabecera cambiada. Enmienda `faithfulness/protocolo_confirmatorio_v1.md` (SHA-256 `4ed610f834806a660efb183481b1ad40cb53117d2c072937c811a249d90135db`) y `faithfulness/enmienda_1_protocolo_confirmatorio.md` (SHA-256 `28afc2f65de0c0cb35ce7ff7c3c9b8cc02b4666eb2c209d16887d872e5f65731`), que no se editan. Se firma como las anteriores: SHA-256, hora en `probes/BITACORA.md`, copia en `faithfulness/`, commit y push. Hay que firmarla antes de elaborar ningún enunciado de las fuentes nuevas.

**Qué se ha visto de los datos.** Lo mismo que al firmar la enmienda 1: conteos de fieles por fuente y una muestra de NL y Lean revisada para comprobar la extracción. Después, el piloto de la opción 3 decidió la etiqueta de 12 infieles del residuo de la copia, sin calcular ninguna métrica. No se ha elaborado ningún enunciado de las fuentes nuevas, no se ha generado ninguna infiel a partir de ellas y no se ha extraído ninguna activación.

---

## 1. El corte sube a 500 orígenes

**Sustituye**, en la Parte A de la enmienda 1, «N = 400» por **N = 500**. El resto de la Parte A queda igual: conteo el día 1 de cada mes, instantánea de formal-conjectures el 1 nov 2027 si no se llega antes y prórroga única hasta el 1 feb 2028.

**Por qué.** Con la hipótesis de tres contrastes de v1, el efecto mínimo detectable con potencia conjunta de 0,8 baja de 0,077–0,090 con 400 orígenes a 0,069–0,081 con 500. Los extremos son correlación perfecta e independencia entre contrastes (tabla de potencia de v1). Detectar un efecto de 0,08 exige entre 362 y 502 orígenes, así que 500 cubre casi toda la horquilla.

El cálculo supone 500 orígenes intercambiables con la varianza por origen del piloto. No modela el reparto por estrato de §3.

## 2. Qué orígenes se analizan

**Elegible** es todo origen que cumpla estas cuatro condiciones:
- elabora en el entorno congelado;
- tiene al menos un par A, B o C3 certificado con el instrumento congelado;
- su fecha pública es posterior a la de los cuatro modelos de la réplica (§5);
- no lo excluye la enmienda 1 (escenario E3 y ningún origen del piloto).

**Un origen por problema.** Si varios orígenes elegibles comparten `grupo_nl` (el mismo NL normalizado), entra uno solo: el del estrato principal si lo hay y, entre los que quedan, el primero en orden de hash. En el núcleo limpio hay 143 grupos con más de una fila (403 filas). Contarlos por separado haría pasar por independiente el mismo problema.

**Orden de hash.** La clave de cada origen es el SHA-256, en hexadecimal, de la cadena UTF-8 `faithfulness:enmienda2:` seguida de su identificador: el `id_origen` del piloto en formal-conjectures y el `id` del corpus de fieles en las demás fuentes. Los orígenes se ordenan por esa clave, de menor a mayor. Cuando hay más elegibles de los que se analizan, entran los primeros de cada estrato. La clave depende solo del identificador. No depende de la etiqueta, del orden de certificación ni de ningún resultado.

**Pares.** De cada origen seleccionado entran todos sus pares certificados de la población primaria, que son como mucho dos por `generar.emparejar`.

## 3. Reparto por fuente

**Dos estratos de análisis:**
- **P**: todo lo que no es NuminaMath-LEAN. Incluye los enunciados de formal-conjectures posteriores al 23 oct 2026, el núcleo limpio de formal-conjectures y de las demás fuentes principales (Parte C de la enmienda 1) y el residuo de la copia (Parte B).
- **M**: NuminaMath-LEAN, el estrato `margen_corto`.

**Tope.** M aporta como mucho el 40 % de los orígenes analizados. Con N = 500, eso son **300 orígenes de P y 200 de M**.

**Cuándo se analiza.** En el primer conteo mensual en que haya al menos 300 orígenes elegibles en P y al menos 200 en M. Ese día se toman los 300 primeros de P y los 200 primeros de M en orden de hash, y el lote se congela con su SHA-256 antes de extraer ninguna activación.

**Si se llega a la fecha límite sin eso** (1 nov 2027, o 1 feb 2028 con la prórroga), entran todos los elegibles de P hasta 300, en orden de hash. De M entran los primeros en orden de hash hasta ⌊2·n_P/3⌋, de modo que M nunca pase del 40 %. La condición de prórroga de v1, menos de 200 orígenes, se cuenta sobre el lote ya recortado.

**Por qué un tope solo para NuminaMath-LEAN.** Es la única fuente que podría llenar el lote por sí sola: con el rendimiento del piloto daría de 1500 a 1700 orígenes. Además, su margen de fechas frente a Qwen3-4B es de 5 días y su tarjeta admite enunciados mal formalizados. Las demás fuentes de P o son formal-conjectures, la población de v1, o son pequeñas: la mayor, IndiMathBench, tiene 312 fieles y daría decenas de orígenes. Un tope del 40 % para cada fuente bloquearía el lote, porque formal-conjectures quedaría en 200 y el resto de P daría previsiblemente de 60 a 90 orígenes (enmienda 1, Parte C), no 100. Con 300 orígenes, P alcanza por sí solo los 300 que pedía el borrador de v1.

**Análisis.** La hipótesis de v1 se evalúa sobre la unión de los orígenes seleccionados, con la fuente y el estrato como estratos del bootstrap, como dice la enmienda 1. No cambia la hipótesis, ni α, ni los contrastes.

**Descriptivos prerregistrados, sin decisión:** los tres contrastes en P solo, en M solo y, dentro de P, en las fuentes de Lean mixto (IndiMathBench y ArXivLean, que parten de un borrador de IA) frente a las de Lean a mano. La procedencia de cada fuente está en `probes/fieles/procedencia_fuentes_2026-11-24.md`.

## 4. Puntajes por fila

El análisis confirmatorio guarda, por cada fila y cada modelo, los puntajes de la sonda `full`, de la sonda `lean_only` y de los dos controles de superficie: superficie cruzada y n-gramas simples. `probes/nivel_b/analizar_pares.py`, en su versión `87d63dc88febf5e83221db0dc44757f0bd582463b78dc433f4c9e54b04c75b6a`, ya los escribe en `puntajes_nivel_b_<modelo>.npz` sin cambiar ningún cálculo. El script que se congele para el confirmatorio tiene que conservar esa salida.

El SHA-256 de cada `.npz` se anota en la bitácora antes de leer ninguna cifra. Con esos puntajes se estima la correlación entre los tres contrastes, que en el piloto no se pudo estimar. Se reporta como descriptivo y no cambia ni N ni la decisión.

## 5. Fechas frente a los cuatro modelos

Las fechas de los modelos son las de `nivel_b_confirmatorio/fechar.py`: Llama-3.1-8B, 2024-09-25; OLMo-2-7B, 2025-01-06; Gemma-3-4B, 2025-03-21; Qwen3-4B, 2025-07-26. Como Qwen3-4B es el más reciente, un enunciado posterior a Qwen3-4B es posterior a los cuatro. Todas las fuentes del núcleo limpio lo son (`probes/fieles/fechas_modelos_2026-11-24.json`, `54a1007d…`).

El margen frente a Qwen3-4B es de menos de una semana en formal-conjectures, FATE-H, FATE-X, NuminaMath-LEAN y formal-imo. Frente a los otros tres modelos es de cuatro meses como mínimo. Si la réplica añade un modelo posterior al 2025-07-26, cada fuente se vuelve a fechar contra él antes de incluirla.

## 6. Lo que no cambia

- La hipótesis, la población, los contrastes, α y las verificaciones de v1.
- Las Partes B y C de la enmienda 1.
- La regla de que no se extrae ninguna activación ni se corre ningún modelo sobre estos orígenes hasta que el lote esté congelado por hash.
