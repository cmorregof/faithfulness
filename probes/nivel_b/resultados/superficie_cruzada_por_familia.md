# Superficie cruzada NL–Lean por familia — Nivel B, qwen3_4b, principal

**EXPLORATORIO, POST HOC.** Es un análisis adicional, pedido después de ver los resultados. No forma parte de la regla de decisión y no cambia la decisión principal.

## Qué se hizo

- Script: `superficie_cruzada_por_familia.py`. Importa `analizar_pares.py` y no lo modifica.
- Datos: índice `datos/pares_indice_principal.jsonl` (377 pares, 256 orígenes) y activaciones `../activaciones/nivel_b_qwen3_4b/`.
- Puntajes OOF de «completo» calculados igual que en el análisis principal: posición «ultimo», capa elegida por CV anidada, 5 semillas y pliegues agrupados por archivo.
- Puntajes OOF de la superficie cruzada: `rasgos_cruzados` + `cruzada`, con las mismas particiones.
- Estadístico: AUROC pareada (`auc_p`).
- IC 95 %: bootstrap de orígenes (`boot_p`, 2000 réplicas, semilla 0), calculado dentro de cada subgrupo.

**Reproducción global:** completo 0,807 [0,766; 0,848]; cruzada 0,688 [0,640; 0,736]; completo − cruzada +0,118 [+0,058; +0,177]. Coincide con el informe.

## Resultados

| Subgrupo (familia de la infiel) | Pares (orígenes) | Completo | Cruzada | Completo − cruzada [IC 95 %] | Precisión 9 |
|---|---|---|---|---|---|
| A | 142 (131) | 0,683 | 0,601 | +0,082 [−0,038; +0,195] | no distinguible de la superficie con estos pares |
| B | 136 (128) | 0,816 | 0,719 | +0,098 [+0,000; +0,195] | no distinguible de la superficie con estos pares (el límite inferior es exactamente 0,000, no queda por encima) |
| C | 99 (89) | 0,927 | 0,829 | +0,098 [+0,006; +0,188] | más allá de la superficie (por poco) |
| C2 (dentro de C) | 68 (63) | 0,913 | **0,933** | −0,020 [−0,103; +0,056] | no distinguible de la superficie con estos pares |
| C3 (dentro de C) | 31 (26) | 0,962 | 0,577 | +0,385 [+0,192; +0,577] | más allá de la superficie (n pequeño) |

**Rasgo de la pista numeral:** fracción de pares en que la infiel tiene más numerales del Lean ausentes del NL que la fiel.

- C2: 84 %.
- C3: 0 %.
- A y B: 0 %.

## Lectura

- **La sospecha se confirma para C2.** La superficie cruzada sola llega a 0,933 en C2, un valor igual o mayor que el de completo (0,913). Las activaciones de C2 no se distinguen de esa pista con estos pares.
- **El +0,427 de C frente a solo Lean no se puede leer como efecto más allá de la superficie.** Frente a la cruzada, el margen de C baja a +0,098. Ese margen sale casi entero de C3 (+0,385), y C3 tiene solo 31 pares en 26 orígenes.
- **A y B:** la diferencia puntual es de alrededor de +0,08 a +0,10, pero ninguno de los dos IC queda entero por encima de 0. Por subgrupo, ninguna de estas dos familias es distinguible de la superficie cruzada con estos pares.
- **Lectura global:** el +0,118 global sigue en pie. Por familia, se distribuye en efectos pequeños que, por separado, no superan la superficie. La excepción es C3, con poca muestra.
- **Advertencia:** el análisis es post hoc, con cinco subgrupos y sin corrección por comparaciones múltiples. Los IC son descriptivos.
