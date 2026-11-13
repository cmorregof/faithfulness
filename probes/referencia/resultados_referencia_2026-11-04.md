# Resultados de la implementación de referencia: Qwen3-4B, 2026-11-04

*Implementación de referencia (Claude Code), independiente de `probes/probe.py`. Según la regla de las 12:55, **no se reporta** hasta compararla con la de Carlos: si difieren más allá del ruido de semilla, se busca el error antes. Preliminar, sin revisión por pares.*

- Regla: `probes/BITACORA.md`, «REGLA DE DECISIÓN» (12:55) y «Precisiones a la regla de las 12:55» (escritas antes de este resultado).
- Corrida: 2026-11-04, 13:13–14:23 (4217 s, 5 procesos en CPU). Números completos: `resultados_referencia_qwen3_4b.json`. Figura: `auroc_por_capa_qwen3_4b.png`.
- Datos: CriticLeanBench (`@6225522b`), activaciones de `probes/activaciones/qwen3_4b/` (Qwen3-4B `@1cfa9a72`, bf16, MPS, plantilla de chat sin razonamiento).
- Etiquetas: de CriticLeanBench (compilador, veredicto de DeepSeek-R1 y revisión humana), no decididas por Lean.
- Configuración: C = 1,0; 5 semillas (0–4) × 5 folds StratifiedGroupKFold por enunciado NL; capa elegida por CV anidada en cada condición; bootstrap de grupos estratificado por clase, 2000 remuestreos, semilla 0; 100 permutaciones.

## Prueba central (450 que compilan: 250 adecuadas / 200 inadecuadas; último token)

| | AUROC | IC 95 % |
|---|---|---|
| Probe completo (NL + Lean) | **0,811** | [0,768; 0,850] |
| Probe solo Lean | **0,723** | [0,677; 0,768] |
| **Diferencia completo − solo Lean** | **+0,088** | **[+0,039; +0,134]** |

**Decisión según la regla: positivo.** El IC de la diferencia queda entero por encima de 0, lo que equivale a una prueba unilateral con α = 0,025.

**Alcance, según la propia regla:** un positivo indica que en las activaciones del prompt completo hay información sobre la etiqueta **más allá del Lean solo**. Eso no muestra por sí mismo que lo decodificable sea la correspondencia NL–Lean; esa la prueban el apilado (abajo) y, sobre todo, el Nivel B.

Dispersión entre semillas (AUROC de cada semilla por separado):
- completo: 0,769; 0,809; 0,784; 0,813; 0,808.
- solo Lean: 0,685; 0,702; 0,707; 0,679; 0,702.
- diferencia: +0,084; +0,107; +0,077; +0,134; +0,107. Las cinco son positivas.

Capa elegida por la CV anidada (25 folds × semillas):
- completo: la 36, la última, en 23 de 25 casos.
- solo Lean: más dispersa (23 ×7, 36 ×6, 35 ×5, 3 ×2, otras).

## Controles

| Control | AUROC [IC 95 %] | Probe completo − control [IC 95 %] |
|---|---|---|
| Etiquetas barajadas, completo (100 permutaciones, con selección de capa) | nulo: media 0,500; percentil 95: 0,550; máximo 0,613 | observado (semilla 0) 0,769; p = 0,0099* |
| Etiquetas barajadas, solo Lean | nulo: media 0,506; percentil 95: 0,562; máximo 0,572 | observado (semilla 0) 0,685; p = 0,0099* |
| Etiquetas barajadas, diferencia | nulo: media −0,006; percentil 95: 0,055 | observado (semilla 0) +0,084; p = 0,0099* |
| Superficie: n-gramas + longitud del Lean | 0,682 [0,632; 0,731] | +0,129 [+0,077; +0,179] |
| Superficie: n-gramas + longitud del Lean y del NL | 0,695 [0,642; 0,742] | +0,117 [+0,068; +0,165] |
| P(Yes) del modelo, prompt completo | 0,699 [0,650; 0,749] | +0,113 [+0,063; +0,160] |

\* 0,0099 = 1/101 es el mínimo posible con 100 permutaciones: ninguna permutación igualó lo observado.

Sobre P(Yes):
- Con el prefijo «**Answer:», la masa de P(Yes) + P(No) es ≈ 1,00.
- El modelo dice «Yes» (P > 0,5) en solo el 2,4 % de las 450 filas, aunque el 56 % son adecuadas.
- Aun así, el orden de P(Yes) separa las clases con AUROC 0,70. El probe completo supera esa respuesta en +0,11.

## Secundarios (se reportan, no deciden)

| Análisis | AUROC [IC 95 %] | Diferencia vs. completo [IC 95 %] |
|---|---|---|
| solo Lean en la misma capa que eligió completo | 0,743 [0,698; 0,788] | completo − esto: +0,068 [+0,022; +0,113] |
| **Apilado (solo Lean + solo NL), regresión logística anidada** | 0,732 [0,685; 0,779] | **completo − apilado: +0,080 [+0,036; +0,124]** |
| solo NL (sin Lean), último token | 0,671 [0,619; 0,722] | — |
| NL desemparejado (Lean con el NL de otra fila), último token | 0,666 [0,615; 0,715] | — |
| P(Yes), solo Lean | 0,637 [0,587; 0,689] | — |
| P(Yes), solo NL | 0,483 [0,427; 0,539] | — |
| P(Yes), NL desemparejado | 0,494 [0,441; 0,546] | — |

Diferencia completo − solo Lean en otros subconjuntos y posiciones:

| Subconjunto / posición | n (adecuadas) | Completo | Solo Lean | Diferencia [IC 95 %] |
|---|---|---|---|---|
| 450, último token (principal) | 450 (250) | 0,811 | 0,723 | +0,088 [+0,039; +0,134] |
| 500 (incluye los 50 que no compilan), último token | 500 (250) | 0,842 | 0,730 | +0,112 [+0,071; +0,156] |
| 450, media sobre el Lean | 450 (250) | 0,767 | 0,665 | +0,101 [+0,065; +0,137] |
| 450 sin las 44 filas dudosas (`X-ni`), último token | 406 (250) | 0,842 | 0,726 | +0,117 [+0,072; +0,161] |

En la posición media sobre el Lean (450): solo NL (media sobre el NL) 0,686 [0,636; 0,735]; NL desemparejado 0,684 [0,635; 0,732].

## Lectura (sin pasar de «separa» / «es decodificable linealmente»)

- **Pregunta principal:** con un probe lineal, la etiqueta es más decodificable con el NL presente que con el Lean solo (+0,088), en las cinco semillas, en los cuatro cortes (450 y 500 filas, media sobre el Lean, sin las dudosas) y por encima de los controles de superficie, de P(Yes) y del nulo por permutación.
- **El apilado no lo explica:** el apilado combina lo que se decodifica del Lean solo con lo que se decodifica del NL solo, y se queda en 0,732. El prompt completo llega a 0,811 (+0,080 [+0,036; +0,124]). O sea, la ganancia no sale de sumar «este Lean parece raro» y «este problema es difícil» por separado. Esto es compatible con que el probe lea algo de la relación entre los dos textos. Aun así no lo prueba, porque el apilado es lineal sobre dos puntajes y las activaciones conjuntas pueden combinar los rasgos de otras formas.
- **El NL ajeno no ayuda:** el Lean con el NL de otra fila (0,666) separa peor que el Lean solo (0,723), y P(Yes) cae al azar (0,49). Ese NL ajeno es del mismo quintil de longitud.
- **Confusor a vigilar: el NL solo separa (0,671).** El enunciado por sí solo trae información sobre la etiqueta (dificultad, fuente o tipo de problema). Por eso el apilado es el control que importa, no solo la diferencia con solo Lean.
- **Dónde aparece:** la curva por capa del completo sigue a la de solo Lean hasta la capa ~9. Desde ahí se separa y crece hasta la última capa (0,816 en la capa 36). La capa elegida es casi siempre la última, la más cercana a la respuesta. La capa 0 da 0,50 en todas las condiciones: es la comprobación de cordura, porque el último token es idéntico en todas las filas.

## Límites

- **Implementación de referencia, sin contrastar todavía con `probe.py`.** No se reporta hasta compararlas.
- **Etiquetas externas y ruidosas.** Son de CriticLeanBench: compilador, DeepSeek-R1 y revisión humana con seis criterios, más amplios que la fidelidad semántica (Peng et al., ACL 2026, Sec. 3.1). No se reporta el número de anotadores ni el acuerdo entre ellos. Sonnet B no identificó error en 44 de los 200 «inadecuados que compilan»; al quitarlas, la diferencia sube (+0,117).
- **No son pares mínimos:** cada problema aparece una vez y el NL solo ya separa (0,671).
- **Un modelo (Qwen3-4B), una plantilla, un idioma de prompt.** Kimina ya está extraído; Goedel, pendiente.
- **Correlacional y lineal.** Que sea decodificable no implica que el modelo use esa información. No hay intervención.
- **Elecciones de la referencia** (escalado, CV interna, bootstrap, superficie, apilado y permutaciones con las particiones de la semilla 0): ver «Precisiones a la regla de las 12:55».
- **Potencia:** el MDE según la regla es ≈ 0,05–0,07. La diferencia observada (0,088) está por encima, pero el límite inferior del IC (0,039) está por debajo del MDE.

## Réplicas: Kimina-Autoformalizer-7B y Goedel-Prover-V2-8B (añadido 2026-11-04, 18:00)

Mismo script, misma regla, mismas particiones y mismos grupos; activaciones de las cuatro variantes en `probes/activaciones/{kimina_7b,goedel_8b}/`. Según la regla, «réplica» = diferencia puntual > 0 con el mismo procedimiento.

| Modelo | Completo | Solo Lean | **Completo − solo Lean** | Completo − apilado | Misma capa | P(Yes) | Perm. de la diferencia (p) |
|---|---|---|---|---|---|---|---|
| Qwen3-4B | 0,811 | 0,723 | **+0,088 [+0,039; +0,134]** | +0,080 [+0,036; +0,124] | +0,068 [+0,022; +0,113] | 0,699 | 0,010 |
| Kimina-7B | 0,747 | 0,705 | **+0,042 [+0,003; +0,083]** | +0,005 [−0,026; +0,038] | +0,015 [−0,026; +0,056] | 0,559* | 0,25 |
| Goedel-V2-8B | 0,802 | 0,758 | **+0,045 [+0,006; +0,084]** | +0,050 [+0,014; +0,085] | +0,069 [+0,034; +0,105] | 0,743 | 0,16 |

\* No interpretable: la masa media de P(Yes)+P(No) es 0,23 (< 0,5).

Otros datos de las réplicas:
- Solo NL: Kimina 0,726; Goedel 0,697.
- NL desemparejado: Kimina 0,688; Goedel 0,699.
- Capa elegida para completo: Kimina, la 19 o la 25 (de 28); Goedel, la 28–30 (de 36).
- Secundarios (diferencia completo − solo Lean): Kimina, 500 +0,071, media sobre el Lean +0,073, sin dudosas +0,045; Goedel, 500 +0,060, media sobre el Lean +0,099, sin dudosas +0,061.

**Lectura.**
- **Los tres modelos replican** según la definición de la regla (diferencia puntual > 0), y los tres IC excluyen 0, aunque en Kimina y Goedel apenas.
- **El efecto es la mitad en los modelos especializados** (+0,04 frente a +0,09).
- **Kimina no supera el apilado ni la misma capa.** Su ganancia se explica por lo que el Lean y el NL aportan por separado.
- **Goedel sí supera el apilado** (+0,050). Su P(Yes) es fuerte (0,743), y aun así la sonda lo supera (+0,060).
- **La diferencia frente al nulo por permutación no es significativa** en Kimina ni en Goedel (p = 0,25 y p = 0,16, con la semilla 0). Ese control es más exigente que el IC por bootstrap, y conviene reportarlo.
- **Goedel-V2 deriva de Qwen3-8B**, así que su acuerdo con Qwen3-4B no es independiente.
- **Kimina tuvo una pausa a mitad de corrida** (SIGSTOP/SIGCONT, por memoria). No cambia el cálculo.

Figuras: `auroc_por_capa_kimina_7b.png`, `auroc_por_capa_goedel_8b.png`. Números: `resultados_referencia_{kimina_7b,goedel_8b}.json`. Igual que en Qwen, **no se reporta** hasta compararlo con `probe.py`.
