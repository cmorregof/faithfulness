# Regla de elaboración v2: recuperar tres grupos de fieles que no elaboran por el entorno

**Estado:** borrador del 24 nov 2026, escrito por Claude Code a pedido de Carlos («Escribe la regla para recuperar las tres»). **No está aprobada y no se ha aplicado.** Se aplica solo cuando Carlos la apruebe citando el SHA-256 de este archivo y el de `probes/fieles/elaborar_v2.py`, que la implementa.

## 1. De qué parte

`probes/fieles/elaborar.py` (`73ad83a6…`) elabora el núcleo limpio en el entorno congelado: Lean 4.34.1 y Mathlib v4.34.1, con las opciones de `certificar.py`. Por la enmienda 1, Parte C, lo que no elabora sale.

A las 08:55, con 21 400 de las 25 870 filas hechas y formal-conjectures aún en curso, había tres grupos de fallos. En los tres falla el entorno, no la formalización.

| Grupo | Filas | Causa |
|---|---:|---|
| `∑ x in s` | 572 (563 NuminaMath-LEAN, 9 IndiMathBench) | Sintaxis de Mathlib que se retiró. La forma vigente es `∑ x ∈ s`. |
| Variables implícitas | 419 (414 NuminaMath-LEAN, 3 IndiMathBench, 1 formal-putnam-like, 1 ArXivLean) | El enunciado usa variables sin declararlas, como `n` o `x`. Con las opciones del certificador (`autoImplicit false`) eso es un error; con las opciones por defecto de Lean, no. |
| formal-imo | 116 de 266 | Sus archivos importan `Imo.ProblemImports`, que trae el elaborador `answer( )` y otras utilidades. La cabecera de `elaborar.py` no las carga. |

Las cifras son las del primer error de cada fila. Una fila puede tener más de una causa. Cuando termine la corrida se recuentan sobre el resultado completo.

## 2. Qué se hace con cada grupo

Se aplica solo a las filas que `elaborar.py` dejó como `no_elabora` con motivo «error de Lean». Las que elaboran no se tocan.

**R1. `∑ x in s` → `∑ x ∈ s`.**
- En el enunciado y en el contexto, dentro del ligador de cada `∑` o `∏` (desde el símbolo hasta la primera coma al mismo nivel de paréntesis), la palabra `in` se sustituye por `∈`. Nada más del texto cambia.
- **Por qué no cambia el enunciado:** en las versiones de Mathlib que aceptaban `∑ x in s, f x`, esa sintaxis era una forma alternativa que daba el mismo término que `∑ x ∈ s, f x`. Se retiró después.

**R2. Formal-imo con su cabecera.**
- Para las filas de formal-imo, la cabecera importa `Mathlib`, `FormalConjecturesForMathlib` y `FormalConjecturesUtil.Deprecated.Answer`. Es lo que trae su `ProblemImports`, salvo dos archivos propios del repositorio (`Imo.ProblemImports.Attributes` e `Imo.ProblemImports.CircularOrder`), que no están en el entorno.
- `answer( )` se elabora en su modo por defecto, que deja la expresión tal cual.
- Si una fila necesita alguno de los dos archivos que faltan, sigue sin elaborar y sale.

**R3. Variables implícitas, solo de una letra.**
- Primero se aplican R1 y R2. Si la fila sigue fallando y algún error lleva la nota de `autoImplicit`, se elabora de nuevo con `set_option autoImplicit true` y `set_option relaxedAutoImplicit false`, solo para esa fila.
- Con `relaxedAutoImplicit false`, solo se ligan solas las variables de una letra (con subíndice o número, como `x₁` o `n2`). Un nombre largo mal escrito sigue siendo un error. Así se evita que una errata se convierta en una variable libre y cambie el enunciado.
- **Por qué es legítimo:** el entorno por defecto de Lean, el de un archivo que solo importa Mathlib, tiene `autoImplicit true`. Con esa opción, el término es el que el autor compiló.
- **Lo que no garantiza:** una variable de una letra que el autor olvidó declarar a propósito con otro tipo queda cuantificada universalmente con el tipo que Lean infiere. Por eso estas filas se marcan.

## 3. Lo que queda escrito en cada fila recuperada

- `lean_elaborado`: el texto que elaboró, que difiere del original solo por R1.
- `recuperada_por`: `R1`, `R2`, `R3` o una combinación.
- `auto_implicit`: verdadero si hizo falta R3.

**El generador y el certificador usan `lean_elaborado`.** Para las filas con `auto_implicit`, el certificador también usa las mismas dos opciones. Eso va en el adaptador v3.1, que se congela por SHA antes de generar ninguna infiel, como exige la enmienda 1.

## 4. Lo que se declara en el análisis

- Las filas recuperadas por R3 se reportan aparte como descriptivo. El análisis de sensibilidad sin ellas va también prerregistrado como descriptivo.
- R1 y R2 no se reportan aparte, porque no cambian el término.
- No se recupera nada más. Los fallos de tipos, instancias, constantes que ya no existen en esta Mathlib (como `Int.coprime_iff_nat_coprime`) y otros errores de sintaxis siguen fuera.

## 5. Cómo se corre

- `probes/fieles/elaborar_v2.py`, que reutiliza la maquinaria de `elaborar.py`: lotes, control positivo con `#check`, filas con contexto propio compiladas solas y auditoría.
- Corre solo sobre las filas de §2 y escribe `datos/fieles/elaboracion/resultados_v2.jsonl` sin tocar `resultados.jsonl`.
- Su SHA-256 y la hora van a la bitácora antes de correrlo.
- No genera infieles ni corre modelos.

**Coste:** unos 1100 enunciados. Las que sigan fallando tras el lote se compilan solas, para leer todos sus errores y decidir R3. Del orden de una a dos horas con dos procesos de Lean.
