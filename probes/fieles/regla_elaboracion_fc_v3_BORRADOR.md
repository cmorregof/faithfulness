# Regla de elaboración v3 para formal-conjectures: el entorno y el contexto del propio repositorio

**Estado:** borrador del 25 nov 2026, escrito por Claude Code tras revisar los 245 enunciados de formal-conjectures que no elaboraron (pedido de Carlos: «Sí, míralos»). **No está aprobada y no se ha aplicado.** No se ha compilado nada nuevo. El script que la implemente se escribe después y se aprueba con su SHA.

## 1. Qué falla y por qué

De las 4804 fieles de formal-conjectures del núcleo limpio, 4559 elaboran y 245 no. La clasificación sale del primer error de cada fila, contrastado con el archivo original en `2207c54d` y con FormalConjecturesForMathlib en los dos commits.

| Causa | Filas | Qué pasa |
|---|---:|---|
| El archivo importa otro archivo de problemas | 122 | 41 módulos, como `ErdosProblems.«1165»` o `Wikipedia.JacobianConjecture`. El entorno no tiene esos módulos y el contexto extraído no trae sus definiciones. |
| ForMathlib más nuevo | 29 | Definiciones que entraron en FormalConjecturesForMathlib después de la copia congelada: `Nat.triangular`, `cliqueTransversalNumber`, `StableMarriage.Unbalanced`… |
| El contexto extraído pierde algo del propio archivo | unas 45 | Teoremas anteriores que el enunciado cita, como `Erdos28.erdos_28`, o un `end` cuyo `namespace` o `section` se perdió. También variables de sección. |
| Otros | unas 50 | Ambigüedades, tipos o instancias. Parte puede ser también de extracción, porque no se miró fila a fila. |

Ninguna de las tres primeras causas está en la formalización. Las tres vienen de nuestro entorno o de nuestra extracción.

## 2. Por qué cambiar ForMathlib no altera lo que ya elabora

- La copia congelada (`corpus_compilar/corpus_lean/FormalConjecturesForMathlib`) es la de `c094b979` con 17 archivos adaptados a Lean 4.34.1.
- Entre `c094b979` y `2207c54d`, FormalConjecturesForMathlib tiene 1301 líneas añadidas y 3 borradas. Las 3 borradas son un `open`, un `import` y una línea de comentario. Ninguna definición existente cambió.
- Los 17 archivos adaptados son idénticos en los dos commits, así que las adaptaciones se conservan tal cual.

## 3. La regla

**F1. Entorno.**
- Una copia nueva, `corpus_compilar/corpus_lean_2207`: el mismo Lean 4.34.1 y el mismo Mathlib v4.34.1 que el congelado.
- FormalConjecturesForMathlib es la copia congelada más los 13 archivos que `2207c54d` añade o modifica (6 nuevos, 7 modificados), sin tocar los 17 adaptados.
- Además, una biblioteca `FormalConjectures` con los 41 módulos de problemas que importan los archivos afectados, y lo que estos importan a su vez, tomados de `2207c54d`.
- Si algún archivo no compila en 4.34.1, se anota y las filas que dependen de él salen.
- Del entorno se guardan el SHA de cada archivo y el `lake-manifest.json`.

**F2. Contexto nativo.** Para cada fila de formal-conjectures, el contexto es el texto del archivo original en `2207c54d`, desde después de los `import` hasta la línea anterior al enunciado (la de la URL del corpus). Incluye los teoremas anteriores con sus pruebas, tal como están en el repositorio. Los imports son los del archivo.

**F3. Se elaboran de nuevo las 4804 fieles de formal-conjectures,** no solo las 245, en `corpus_lean_2207` con F2 y la misma maquinaria de `elaborar.py`: lotes, control positivo con `#check`, filas con contexto propio compiladas solas y auditoría. Formal-imo, que importa ForMathlib por R2, se repite también.

**Control de regresión.**
- Se informa cuántas de las 4559 que elaboraban siguen elaborando.
- Una fila que elaboraba antes y ahora no se anota con su error. Sale, porque desde esta regla el entorno de formal-conjectures es `corpus_lean_2207`.
- Una fila que elabora en los dos entornos y cuyo texto Lean cambia con el contexto nativo conserva el texto nuevo, que es el del repositorio.

## 4. Lo que implica para el resto del protocolo

- **El certificador de las filas de formal-conjectures tiene que correr en `corpus_lean_2207` y con el contexto nativo.** Va en el adaptador v3.1, que se congela por SHA antes de generar ninguna infiel.
- **Lo mismo pasará con los enunciados posteriores al 23 oct** (la población original de v1). Usarán definiciones de ForMathlib que la copia de octubre no tiene. Esta regla deja resuelto el entorno hasta `2207c54d`. Cada instantánea posterior necesitará el mismo paso: ForMathlib y los módulos de problemas de la instantánea, con la misma comprobación de que solo se añadieron definiciones. Si alguna definición existente cambiara de significado, se para y se pregunta.
- Las demás fuentes (NuminaMath-LEAN, IndiMathBench, etc.) solo importan Mathlib, que no cambia. Sus resultados se quedan como están.

## 5. Coste y lo que no se sabe

- **Coste:** compilar los 13 archivos de ForMathlib y unos 41 a 60 módulos de problemas, y después elaborar unas 5000 filas. Del orden de 2 a 3 horas con dos procesos de Lean junto a T1. No hace falta descargar nada, porque el clon local tiene `2207c54d`.
- **Recuperación esperada:** de las 245, entre 150 y 200 (las tres primeras causas suman unas 196). Es una estimación sin compilar.
- **Riesgo:** el contexto nativo incluye pruebas reales de teoremas anteriores, que pueden ser lentas. Los límites de tiempo son los de `elaborar.py`. También está pendiente el fallo de `elaborar.py` en que un lote pasó del límite de 30 minutos sin cortarse. El script nuevo vigilará el tiempo de cada proceso de Lean por su cuenta.
