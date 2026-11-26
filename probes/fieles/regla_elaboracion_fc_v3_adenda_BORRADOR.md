# Adenda a la regla de elaboración v3 para formal-conjectures

**Estado:** borrador del 25 nov 2026, escrito por Claude Code al preparar el script de la regla v3 (`regla_elaboracion_fc_v3_BORRADOR.md`, 11883ca0…, aprobada por Carlos con «Apruebo, escríbelo»). **No está aprobada y no se ha aplicado.** No se ha compilado nada. Se aplica junto con `probes/fieles/elaborar_fc_v3.py`, y las dos se aprueban citando sus SHA-256.

La regla v3 no decide cinco puntos que el script necesita. Uno cambia el entorno. Los otros cuatro precisan cómo se aplica.

## A1. También se actualiza un archivo de FormalConjecturesUtil

**Lo que pasa.** En `2207c54d`, 1096 declaraciones del repositorio van precedidas de `set_option linter.style.formal_proof_palomar false in`. Esa opción la registra `FormalConjecturesUtil/Attributes/Basic.lean`, que cambió entre `c094b979` y `2207c54d`. La copia congelada no la tiene, y con ella cada una de esas líneas da el error «unknown option».

**Cuánto pesa.** 769 de las 4804 filas tienen la opción en su contexto nativo, y 726 de ellas elaboran hoy con el contexto extraído. También la usan 19 de los 47 módulos de problemas que hay que compilar. Sin este cambio, la regla v3 haría perder esas 726 filas en lugar de recuperar las 245.

**La regla.** `FormalConjecturesUtil/Attributes/Basic.lean` se sustituye por su versión de `2207c54d`. Es el único archivo de FormalConjecturesUtil que cambió entre los dos commits, y la copia congelada es idéntica a la de `c094b979`, así que la sustitución es limpia.

**Por qué no cambia el significado de nada.** El cambio tiene 48 líneas añadidas y 3 borradas. Registra la opción y añade una comprobación de que, en un problema `research solved`, el enlace de `formal_proof` apunte al registro Palomar. Las 3 líneas borradas son una línea de documentación y dos ejemplos. No define ningún objeto matemático, y la comprobación solo mira metadatos.

## A2. La cabecera de cada archivo de elaboración

- El archivo de elaboración no es un módulo. Importa `Mathlib`, `FormalConjecturesForMathlib` y `FormalConjecturesUtil`, como en `elaborar.py`, más los imports propios del archivo original sin las palabras `public` y `meta`. Los imports de Mathlib se omiten, porque `import Mathlib` los cubre.
- **Por qué equivale a los imports del archivo.** En `2207c54d`, `FormalConjecturesUtil` importa en público `Mathlib` y `FormalConjecturesForMathlib`, así que el entorno es el mismo. Un archivo que no es módulo importa todo, también lo privado.
- **Por qué no importa que no sea módulo.** En Lean 4.34.1, `public` y `@[expose]` solo actúan entre módulos. Lo dice la documentación de `expose` en `Lean/Elab/MutualDef.lean`, y `Lean/Elab/DeclModifiers.lean` lo aplica así. Dentro de un mismo archivo, el sistema de módulos no cambia el término de ningún enunciado.

## A3. El enunciado y lo que lo precede

- El enunciado es el campo `lean` de la fila, sin cambios. En 1594 filas ese campo tiene `sorry` donde el repositorio tiene una prueba. La URL marca exactamente las líneas del enunciado con su prueba.
- El contexto nativo termina en la línea anterior a la URL. Por eso incluye el docstring, los atributos y los `open … in` o `set_option … in` del propio enunciado, que se aplican a él como en el repositorio. En el contexto extraído esas líneas faltaban.

## A4. Un error en el contexto cuenta

- Como en `elaborar.py`, una fila no elabora si hay cualquier error en su archivo. Eso incluye un error en el contexto nativo, como la prueba de un lema anterior que dejó de compilar entre la Mathlib del repositorio y la v4.34.1.
- Cada fila que falla sola guarda dónde está su primer error: en el contexto, en el enunciado o en el control. Así se puede contar cuántas salen solo por el contexto y decidir después si eso merece otra regla.

## A5. Las reglas v2 se aplican igual

- Si una fila de formal-conjectures no elabora con su contexto nativo y el motivo es «error de Lean», se le aplican R1 y R3 de la regla v2 (7fe61f22…), como al resto del núcleo. R2 es solo para formal-imo.
- formal-imo se repite en `corpus_lean_2207`. Las 255 filas que elaboran se compilan con su texto elaborado y, si tienen `auto_implicit`, con las opciones de R3. Las 11 que no elaboraban pasan otra vez por v1 y v2, cada una sola.

## Lo que queda escrito

- El entorno se construye en `corpus_compilar/corpus_lean_2207`, una copia del congelado hecha con clonado de APFS, sin descargar nada. Su lista de archivos con SHA-256, los módulos que compilan y los que no, y los registros de `lake` van en `datos/fieles/elaboracion/fc_v3/`.
- El resultado va a un archivo nuevo, `datos/fieles/limpias_qwen3_4b_elaboradas_v3.jsonl`, con el campo `entorno` en cada fila. Las filas de formal-conjectures llevan su contexto nativo y sus imports. El archivo anterior (2298ad90…) no se toca.
- El clon de formal-conjectures pasa del directorio temporal a `corpus_compilar/formal_conjectures.git`, para que no se pierda.
