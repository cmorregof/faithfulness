# Adenda 2 a la regla de elaboración v3: cada fila sola

**Estado:** borrador del 25 nov 2026, escrito por Claude Code tras la muestra de 100 filas de `elaborar_fc_v3.py` (7531433b…). **No está aprobada y no se ha aplicado.** Se aplica con la nueva versión de `probes/fieles/elaborar_fc_v3.py`, y las dos se aprueban citando sus SHA-256.

## Qué mostró la muestra

- **Recuperación.** De 50 filas que no elaboraban, 44 elaboran ahora con el contexto nativo, sin R1 ni R3. Las 50 que ya elaboraban siguen elaborando.
- **Las 6 que siguen fuera** fallan en su contexto, no en el enunciado. En los seis casos la causa es la diferencia entre la Mathlib del repositorio y la v4.34.1, como prevé A4:
  - `IsCarmichael`, ambiguo entre la definición de ForMathlib y la de Mathlib;
  - la notación `d⁄dX`, que ya no se lee igual (dos filas);
  - una prueba anterior que dejó de compilar (tres filas de `MovingSofa`).
- **La auditoría encontró un falso positivo del lote.** Se compilaron solas 10 filas que habían elaborado en lote. Una, de `Wikipedia/WallSunSun`, no elabora sola. Su contexto reabre `namespace QuadraticAlgebra`, un namespace que ya existe en Mathlib. Sola, `discr` se resuelve como `QuadraticAlgebra.discr` y da un error de tipos. En el lote, el envoltorio `namespace Fiel_<j>` convierte ese namespace en `Fiel_<j>.QuadraticAlgebra`, así que `discr` se resuelve como otra constante, que sí encaja. **El envoltorio cambió qué constante nombraba el contexto.**

Ese es el riesgo que importa. El lote puede dar por bueno un texto que solo no elabora, o uno que elabora con otro significado. Con el contexto nativo pasa más a menudo que con el extraído, porque los archivos del repositorio reabren namespaces de Mathlib (`Nat`, `SimpleGraph`, `QuadraticAlgebra`…).

## La regla

**B1. Sin lotes en formal-conjectures ni en formal-imo.** Cada fila se elabora en su propio archivo, con la misma cabecera, el mismo control positivo `#check` y las reglas R1 y R3 si falla. Sin lotes no hay envoltorio, y por tanto no hace falta auditoría. Sustituye a F3 en lo que se refiere a los lotes.

**B2. Las demás fuentes que pasaron en lote con un namespace en su contexto.** En v1 y v2, 239 filas del resto del núcleo elaboraron en lote y tienen un `namespace` en su contexto: 127 de NuminaMath-LEAN, 98 de FATE-X y 14 de LeanCat. Se elaboran de nuevo solas en el entorno congelado (`corpus_lean`), con el texto que elaboró, y decide esa corrida. Las que no elaboren solas salen del archivo v3.

**B3. Una auditoría de las demás.** Hay otro mecanismo posible. Una instancia o una notación global del contexto de una fila sigue activa en las filas siguientes del mismo lote. Para medirlo, 200 de las 19 736 filas restantes que elaboraron en lote se compilan solas en el entorno congelado, elegidas por sorteo con semilla fija. Es solo informativo, como la auditoría de v1, y ningún veredicto cambia. Si alguna difiere, se para antes de escribir nada más y se pregunta.

## Coste

- Sola, una fila tarda unos 9 s con el entorno ya cargado; una que falla y prueba R1 o R3, unos 30 s.
- formal-conjectures: 4804 filas con dos procesos de Lean, unas 6 a 7 horas.
- formal-imo, B2 y B3: unos 45 minutos más.
- La corrida es reanudable en formal-conjectures.
