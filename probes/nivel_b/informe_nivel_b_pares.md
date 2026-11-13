# Nivel B, pares mínimos certificados: informe — 6 nov 2026

**Estatus: EXPLORATORIO, lote de desarrollo.** El prompt de Carlos del 4 nov (22:29) define así los pares v3. La prueba principal del Nivel B iba a ser la de tripletas; hoy no hay un lote de tripletas certificable (ver la bitácora).

*Preliminar, sin revisión por pares. No se ha comparado con `probe.py` de Carlos.*

## Regla y datos
- **Regla:** `regla_borrador.md` (SHA `d2236454…`) más `precisiones_regla_nivel_b_2026-11-05.md`, con la precisión 9 de Carlos. Ambas fueron aprobadas por Carlos el 5 nov a las 22:44, antes de cualquier resultado.
- **Lote:** el registrado `7dd3b052…`, certificado con Lean 4.34.1.
  - 408 pares certificados (parquet `fb80e4b2…`).
  - Exclusiones de `datos/exclusiones_nivel_b.json`, fijadas antes de extraer activaciones.
  - **Principal:** 377 pares en 256 orígenes.
- **Modelo:** Qwen3-4B, último token.
  - Capa elegida por CV anidada.
  - Pliegues agrupados por archivo.
  - Estadístico: AUROC pareada, con bootstrap de orígenes (2000).
  - 100 permutaciones de roles dentro de cada par.

## Resultado

| Análisis | Pares (orígenes) | Completo | Solo Lean | **Diferencia [IC 95 %]** | Decisión |
|---|---|---|---|---|---|
| **Principal** | 377 (256) | 0,807 | 0,582 | **+0,225 [+0,158; +0,291]** | **POSITIVO (potencia reducida)** |
| Sensibilidad: los 408 | 408 (270) | 0,820 | 0,607 | +0,213 [+0,150; +0,280] | positivo |
| Sensibilidad: sin los pares 4, 45, 56, 203 | 373 (252) | 0,800 | 0,585 | +0,214 [+0,147; +0,284] | positivo |

- **Permutaciones del principal:**
  - p de completo = 0,0099;
  - p de la diferencia = 0,0099, el mínimo posible con 100 permutaciones.
- **Potencia reducida:** el número de pares supera el mínimo de 200, pero los orígenes quedan por debajo de 300.

## Controles (principal; se reportan, no deciden salvo la condición 6)

| Control | Valor |
|---|---|
| **Superficie cruzada NL–Lean** (condición 6 y precisión 9) | cruzada 0,688; **completo − cruzada = +0,118 [+0,058; +0,177]** |
| Superficie: n-gramas del Lean y del NL | 0,729; completo − superficie = +0,078 [+0,010; +0,141] |
| **P(Yes) del modelo** | **0,839**; completo − P(Yes) = −0,032 [−0,074; +0,008] |
| NL desemparejado | 0,508 [0,459; 0,561] |
| Solo NL | 0,500 (por construcción; comprueba la tubería) |
| media_lean (posición secundaria) | completo 0,944, solo Lean 0,780, diferencia +0,164 [+0,120; +0,210] |

**Lo que dicen estos controles:**
- **Superficie cruzada:** la condición del positivo se cumple. Por la precisión 9, como el IC queda entero por encima de 0, **se puede escribir que el efecto va «más allá de la superficie» cruzada NL–Lean.** Se cumple también en las dos sensibilidades: +0,144 y +0,112.
- **P(Yes):** la respuesta sí/no del propio modelo separa tan bien como el probe lineal; en el principal, algo mejor. En las sensibilidades da −0,001 y −0,041, con IC que incluyen 0. **Aquí el probe no añade nada sobre lo que el modelo dice.** Es la diferencia más clara con el Nivel A y el Nivel C, donde el probe sí superaba a P(Yes).
- **Original frente a fiel** (corregido el 6 nov):

| Análisis | P(original > fiel) | P(original > infiel) |
|---|---|---|
| Principal | 0,520 | 0,809 |
| Los 408 | 0,578 | 0,826 |
| Sin dudosos | 0,524 | 0,843 |

  El original se puntúa como una fiel. La señal no es «haber sido editado».

## Subconjuntos (se reportan, no deciden)

| Subconjunto | Pares | Diferencia [IC] (principal) | P(Yes) |
|---|---|---|---|
| Familia A (más fuerte) | 142 | +0,141 [+0,038; +0,248] | 0,725 |
| Familia B (más débil) | 136 | +0,129 [+0,027; +0,230] | 0,852 |
| Familia C (otro teorema) | 99 | +0,427 [+0,320; +0,539]; solo Lean 0,500 | 0,904 |
| Sin C2 | — | +0,187 [+0,112; +0,260] | 0,812 |
| Infiel verdadera (fidelidad ≠ verdad) | 181 | +0,185 [+0,098; +0,277] | 0,860 |

**Familia C:** que solo Lean dé 0,500 no es un error. Las activaciones difieren en los 99 pares. Las ediciones C (N → N+1, operador invertido) no dejan rastro leyendo solo el Lean, así que solo Lean en el azar es lo esperable.

**Pero el +0,427 no se interpreta todavía.** En C2, el numeral nuevo suele faltar en el NL; es una pista cruzada de superficie que no está desglosada por familia. En la sensibilidad sin dudosos, la familia B baja a +0,100 [−0,000; +0,208].

## Lectura, sin pasar de lo que permite la regla
Dentro del mismo problema (mismo NL), y en pares certificados por Lean, las activaciones del prompt completo separan la formalización fiel de la infiel mejor que las del Lean solo. **Es decodificable linealmente más allá del Lean solo y más allá de la superficie cruzada NL–Lean.** Esto se sostiene en las tres variantes del lote.

Dos matices acotan la conclusión:
1. **Es exploratorio:** es el lote de desarrollo.
2. **La propia respuesta sí/no del modelo (P(Yes)) separa igual de bien.** El resultado no muestra información latente que el modelo «no diga»; muestra que la separación más allá del Lean está en las activaciones y también en su respuesta.

## Límites
- **Exploratorio y en potencia reducida:** 256 orígenes, por debajo de los 300.
- **Compuerta de superficie:** sobre los certificados da 0,706, con exceso 0,081. No pasa, y se declaró exploratoria.
- **Etiquetas:** vienen del generador, certificadas por Lean.
  - La revisión de confirmación encontró originales no fieles y «equivalentes de hecho»; se excluyeron antes de extraer.
  - La revisión fue hecha por un modelo (Opus), no por un humano.
- **Solo un modelo y una plantilla.** Lineal y correlacional.
- **Sin comparar con `probe.py`.**

## Añadido el 6 nov (post hoc, exploratorio): superficie cruzada por familia

Ver `resultados/superficie_cruzada_por_familia.md`.

| Subgrupo | Pares | Completo − cruzada [IC 95 %] |
|---|---|---|
| A | 142 | +0,082 [−0,038; +0,195] |
| B | 136 | +0,098 [+0,000; +0,195] |
| C | 99 | +0,098 [+0,006; +0,188] |
| C2 | 68 | −0,020 [−0,103; +0,056] |
| C3 | 31 | +0,385 [+0,192; +0,577] |

- **Global:** el resultado sigue en +0,118 [+0,058; +0,177], positivo como fija la regla.
- **Por familia:** A, B y C2 son «no distinguibles de la superficie con estos pares» (precisión 9 aplicada por subgrupo, de forma descriptiva). Solo C3 (31 pares) supera claramente la superficie.
- **Familia C:** el +0,427 frente a solo Lean viene sobre todo de la pista cruzada del numeral de C2. No se interpreta como efecto más allá de la superficie.
 