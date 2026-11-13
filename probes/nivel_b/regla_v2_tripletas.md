# Nivel B por tripletas — regla v2 (BORRADOR 3, SIN APROBAR)

Borrador escrito la noche del 4 nov 2026 (sesión lateral de la orquestadora). **El texto de esta regla de análisis no está aprobado: lo aprueba Carlos.**

Hacia las 23:3x, Carlos eligió la opción «b» del §8 del borrador 1: reglas fieles NUEVAS de operador. También delegó en una revisión independiente (un Opus, y luego un Fable que verifica al Opus) la aprobación de las **reglas del generador** de tripletas, y solo de eso. No cubre:
- certificar con Lean;
- registrar nada en `prometeo_lean/aprobados/`;
- crear marcas `APROBADO_*`;
- aprobar este texto.

**Reglas del generador: revisadas** por Opus (`tripletas/revision_reglas_E_opus.md`) y verificadas por Fable (`tripletas/revision_reglas_E_fable.md`). Las dos dicen «aprobar con correcciones», y las correcciones obligatorias O1–O13 están aplicadas (§1, §8). El SHA final de `tripletas_100.jsonl` es **1ea02c35271799e94e00a44bea3e47320912a9067bc38ff29229e0a401eddcec**.

Material: `probes/nivel_b/tripletas/` contiene `reglas_fieles_nuevas.py` (E1–E7), `filtros_infieles.py` (O7–O10), `generar_tripletas.py`, `medir_superficie.py`, `tripletas_100.jsonl`, `resumen_tripletas_100.json`, `muestra_tripletas_30.md`, `elegibles_pares_FX.jsonl` y `medicion_superficie.json`. El SHA vigente está en `resumen_tripletas_100.json` y en la bitácora. El borrador 1 (`tripletas_100.jsonl` 22147b60…) se conserva en `tripletas/historico_22147b60/`. El borrador 2 previo a la revisión (74c1afd5…) se sobrescribió al regenerar. Lo que queda de él es el volcado que usó Fable y los números de línea de los dos informes.

## 0. Por qué

En el lote v3, un modelo que lee solo el Lean separa la variante fiel de la infiel con AUROC pareada de 0,758 (455e20ed…; 0,744 en el 7dd3b052… vigente). Lo que queda es la convención: una edición infiel produce una forma atípica respecto al estilo de Mathlib, y un lector del Lean aprende que «atípico = infiel». La tripleta pone una forma atípica **también del lado fiel** y hace que se parezca a la de la infiel. La pregunta pasa a ser si el probe separa lo fiel de lo infiel dentro del mismo enunciado mejor que un modelo de superficie.

## 1. Unidad: la tripleta

Unidad = **enunciado de origen** (`id_origen`; fuentes de `generar.cargar_origenes()`: FormalMATH-Lite y formal_conjectures), con el nombre del teorema neutralizado (`theorem T`). Para cada enunciado:

- **(a) O**: el Lean original (se supone fiel al NL; la pregunta P0 de la revisión lo comprueba).
- **(b) F, fiel atípica**: una reescritura fiel de O. Puede venir de una regla D de `reglas_generador.md` (D8, D1, D1c, D7, D2, D5, D4c, D4h, D3, D6) o de una regla **nueva E1–E7**:
  - E1, simetría de `=`;
  - E2, simetría de `≠`;
  - E3, `∧` en una hipótesis;
  - E4, `∨`;
  - E5, espejo de un átomo de orden en cualquier posición;
  - E6, desplazamiento de la cota en ℕ/ℤ en cualquier posición;
  - E7, `0 < t` ↔ `t ≠ 0` en ℕ.

  Las E están definidas en `reglas_generador.md`, sección «Reglas fieles nuevas para tripletas». Cada E se prueba en todos sus sitios (hasta 8 por regla). Una F cuyo texto repite otro candidato del mismo origen se descarta. Etiqueta esperada: adecuada.
- **(c) Infieles**: como mucho una por familia A/B/C (reglas A1, A2, A3, B2, B3, B4, C1, C2, C3 de `generar.py`, con los filtros de v3; **B1 fuera**, por la huella de su numeral). Cada una en dos versiones: **X(O)** (pura) y **X(F)** (la misma regla aplicada a F). Etiqueta esperada: inadecuada. Antes de armar la tripleta se descartan:
  - las ediciones vacuas detrás de `∀ …,`;
  - por la revisión (`filtros_infieles.py`):
    - **S**: B2/C3 sobre un átomo de signo de una variable ligada por ∃ (testigo degenerado);
    - **H**: A2/A3/B2/B3/C3 sobre una relación con una **variable de holgura** que absorbe el cambio, lo que deja la variante equivalente al original o trivial;
    - **E∃**: B2/C3 bajo un ∃ de la conclusión (de las C3 de ese tipo, la mayoría eran triviales);
    - **N**: C2 cuyo numeral aparece más de una vez en su zona (variante mal tipada o contradictoria).

  También se excluyen por nombre los orígenes con un original no fiel o equivalente: FM[286] y FM[181] (conclusión `True`), Erdos274 *abelian* (A1 quita una hipótesis redundante) y FM[240] (`ε` libre en la conclusión).

**Cuadrado conmutativo (obligatorio).** X(F) es O con las dos ediciones aplicadas. Si los tramos de F y de X en O no se solapan, X(F) tiene que ser igual a O con ambos tramos. Si se solapan, algún sitio de la regla de F aplicado a X(O) tiene que dar X(F). Una familia sin cuadrado no entra.

**Imitación.** La *firma* de una edición son las clases de token que quita y las que pone, como multiconjuntos: numeral → NUM, identificador → ID, operadores tal cual; reordenar no cuenta. La *imitación* de (F, X) es el número de clases que comparten las dos firmas. Ejemplos:
- E5 `a ≤ b` → `b ≥ a` y C3 `a ≤ b` → `a ≥ b` quitan `≤` y ponen `≥`: imitación 2, firma igual;
- E6 `3 ≤ k` → `2 < k` y C2 `3 ≤ k` → `4 ≤ k` quitan y ponen un numeral: imitación 2.

**Elección** (determinista, semilla `20261104:tripletas:<id_origen>`):
- Para cada F posible, y para cada familia, se elige la X pura con mayor (imitación, coincidencia de sitio, sorteo).
- Se elige la F con mayor:
  1. imitación máxima;
  2. nivel de operador (operador: E6, D8, E7, E5, D1, D1c, E1, E2; luego las demás; los renombres D3/D6 al final);
  3. número de familias;
  4. coincidencia de sitio;
  5. orden de preferencia;
  6. sorteo.
- **Comparación principal del enunciado**: la familia con mayor (imitación, coincidencia, sorteo); queda marcada `comparacion_principal`.

## 2. Lote de desarrollo y lote de prueba

- **Lote de desarrollo**: los orígenes con par en `candidatos_v3.jsonl` vigente (7dd3b052…, 890 pares, 583 orígenes), en `v3_previo/candidatos_v3_previo.jsonl` (bd9944d2…, 590) y en las copias intermedias 455e20ed… y 219c6ba7… (584 cada una; en el scratchpad 854e7f7d de la sesión que las generó). Además, por nombre, `OeisA211417.general_divisibility` y `FormalMATH_lite[286]`. Unión: **590 orígenes**.
- **Todo lo que se ajusta se ajusta solo en el lote de desarrollo** (probe, modelo de superficie, escalas) y se **congela** (archivo y SHA en la bitácora) antes de extraer activaciones de las tripletas.
- **Lote de prueba**: las tripletas. Se excluyen los orígenes del lote de desarrollo y los que tienen un Lean textualmente idéntico (nombre neutralizado) a uno de ellos. Las dos cosas se comprueban con `assert`.

## 3. Selección de los 100 enunciados

**Estratos.** La selección es estratificada por la imitación máxima de la tripleta (2, 1, 0 con F de operador, 0 con otra F) y, dentro de cada uno, por si hay familia A o B. Cada estrato se baraja con la semilla `20261104:tripletas` y se llena en orden hasta 100.

**Elegibles (versión final): 688.** Antes de los filtros de la revisión eran 1009.

| Estrato | Con A o B | Solo C |
|---|---:|---:|
| Imitación 2 | 13 | 59 |
| Imitación 1 | 25 | 0 |
| Operador sin imitación | 3 | 486 |
| Otra F | 6 | 96 |

Los filtros descartan, entre todos los intentos sobre los elegibles: N 406, E∃ 59, H 32, S 8 y vacuas tras ∀ 7.

**Composición de las 100** (SHA 1ea02c35…):
- F: E6 59, E5 38, E1 3.
- Comparación principal: E6~C2 59, E5~C3 13, E5~A2 9, E5~A3 8, E5~B3 8 y una de cada una de E1~C2, E1~A1 y E1~A2. Por familia: C 73, A 19, B 8. Por imitación: 2 en 72, 1 en 25, 0 en 3.
- Infieles puras: A 30, B 12, C 88, cada una con su compuesta.
- 83 de formal_conjectures y 17 de FormalMATH-Lite, en 86 archivos.

Tamaño de edición: contado con expresión regular, no con el tokenizador (`transformers` no se carga esta noche).

## 4. Métrica principal: exactitud dentro del par, probe frente a superficie

**Comparación principal**: una por enunciado, (F, X_p(O)), con X_p la infiel marcada `comparacion_principal`. Los dos miembros están a una edición del original y, por construcción, las dos ediciones quitan y ponen las mismas clases de token. Son 100 comparaciones en 100 enunciados.

- Un modelo **acierta** si puntúa F estrictamente más alto que X_p(O). **Un empate cuenta como fallo.**
- **Exactitud dentro del par** = fracción de enunciados en que acierta, con IC 95 % de Wilson y por bootstrap de enunciados (10 000, semilla fija).
- Modelos: el **probe** (logit del probe congelado sobre las activaciones de la variante completa, NL + Lean) y el **modelo de superficie congelado** del §5 (que lee solo el Lean).

**McNemar.** Como hay una comparación por enunciado, el agrupamiento por enunciado es trivial y McNemar es el estándar:
- *b* = número de enunciados en que **acierta el probe y falla la superficie**;
- *c* = número de enunciados en que **falla el probe y acierta la superficie**;
- los concordantes no cuentan;
- se usa la prueba binomial exacta bilateral de *b* frente a Bin(*b* + *c*, ½).

Se informan *b*, *c* y las dos exactitudes.

**McNemar agrupado, para todas las comparaciones puras** (secundario, de 1 a 3 por enunciado; Durkalski et al., 2003). Para cada enunciado *i*:
- *n₁₀,ᵢ* = número de comparaciones en que acierta el probe y falla la superficie;
- *n₀₁,ᵢ* = número de comparaciones en que falla el probe y acierta la superficie;
- *dᵢ* = *n₁₀,ᵢ* − *n₀₁,ᵢ*.

Estadístico: X² = (Σ dᵢ)² / Σ dᵢ², con 1 grado de libertad. Se da también la versión por permutación de signos de *dᵢ* (100 000, semilla fija, bilateral).

- **Criterio (propuesta, la fija Carlos):** «el probe separa más allá de la superficie» si su exactitud es mayor y p < 0,05 en la prueba principal.
- Sensibilidades (no deciden):
  - agrupando por archivo;
  - por combinación (E5~C3, E6~C2);
  - por familia;
  - por zona;
  - por fuente.
- Potencia: con 100 comparaciones, McNemar detecta diferencias de discordancia grandes; si Carlos lo pide, se calcula antes de mirar los datos.

**Secundarias del cuadrado** (misma prueba; no deciden): (F, X(F)), (O, X(O)) y los efectos factoriales por cuadrado:
- contenido = [s(O) + s(F) − s(X(O)) − s(X(F))] / 2;
- forma = [s(F) + s(X(F)) − s(O) − s(X(O))] / 2.

Solo entran las comparaciones cuyos miembros están **certificados** (§6). Como sensibilidad, se repite con todas.

## 5. Secundario: análisis emparejado por δ con superficie congelada

- **Modelo de superficie**: regresión logística (C = 1) sobre unigramas y bigramas binarios del Lean (tokenización de `compuerta_superficie.py`, sin `import`). Se entrena **una vez** con los pares del lote de desarrollo vigente (`candidatos_v3.jsonl`: certificados si existe la certificación, si no, el emparejamiento provisional). Se guarda con su SHA y **nunca se reajusta**.
- Para cada comparación (F, X(O)):
  - δ = logit_sup(F) − logit_sup(X(O));
  - Δ = logit_probe(F) − logit_probe(X(O)).

  Cada logit se divide por la desviación típica de los logits de ese modelo en el lote de desarrollo, fijada al congelar.
- Análisis:
  - (i) exactitud del probe donde δ ≤ 0;
  - (ii) Δ = α + β·δ con errores agrupados por enunciado: α es la preferencia del probe por la fiel cuando la superficie no distingue;
  - (iii) exactitud por terciles de δ, con cortes fijados en el lote de desarrollo.
- Lectura: si α > 0 con un IC que no cruza 0, la distinción fiel/infiel es decodificable linealmente de las activaciones más allá de la superficie del Lean.

## 6. Certificación y fracción no decidida

- Con `certificar.py`, cuando Carlos la apruebe: F «equivalente» con O; X(O) y X(F) «no_equivalente», con el criterio de nivel del §6 de `reglas_generador.md`.
- **Antes de certificar hay que adaptar `certificar.py`**:
  - no conoce E1–E7;
  - no conoce las compuestas `X∘E*`;
  - para átomos bajo un ligador, la pieza tiene variables ligadas libres y hay que certificarla cuantificada (`∀ n, (P n ↔ P' n)`) o con el enunciado entero (`forall_congr'`).

  Esta noche no se toca.
- **Fracción no decidida** (`sin_decidir` + `no_elabora`): se reporta por familia, regla, tipo (pura o compuesta) y regla de F. También frente a proxies de dificultad: **longitud del Lean** (caracteres y tokens, en terciles), **número de hipótesis** (0, 1, 2, 3 o más) y **fuente**, con una regresión logística descriptiva. Los proxies están en cada tripleta (`proxies`). Se reporta siempre junto a la métrica principal.

## 7. Compuerta de superficie: EXPLORATORIA

La compuerta que Carlos eligió a las 17:58 (criterio «firma», `probes/BITACORA.md`) **no bloquea**; se reporta. En v3 (455e20ed…) dio solo-Lean 0,758 y exceso 0,169 (no pasaba); en el 7dd3b052… vigente, 0,744 y 0,157.

## 8. Medición de superficie del diseño (diagnóstico, no la métrica)

`medir_superficie.py`: regresión logística sobre unigramas y bigramas del Lean, con validación cruzada de 5 pliegues agrupada por archivo, entrenada y evaluada **dentro de las tripletas elegibles**. Mide si la etiqueta de las tripletas se lee de la forma del Lean. Las columnas son las tres versiones: el borrador 2 antes de la revisión, sobre 1009 elegibles; la versión final, sobre 688 elegibles; y el borrador 1.

| Diseño | Borrador 2 (pre-revisión) | **Final** | Borrador 1 (D3/D6) |
|---|---:|---:|---:|
| (F, X(O)), todas | 0,89 | 0,88 | 0,99 / 1,00 |
| Comparación principal, todos los elegibles | 0,88 | 0,88 | |
| (O, X(O)) estilo v1 / (F, X(F)) estilo v3 | 0,80 / 0,81 | 0,77 / 0,78 | |
| Imitación ≥ 2 | 0,63 | 0,67 | |
| **Comparación principal de las 100** (CV entre ellas, n = 100, ruidoso) | 0,64 | **0,735** | |

La versión final lee peor que el borrador 2 porque los filtros obligatorios quitaron justo las parejas que mejor imitaban: las E5~C3 bajo ∃, que eran triviales (de 53 principales quedan 13). Se probó también la corrección opcional P1 (distinguir en la firma los numerales que están en el NL de los que no). Daba 0,785 en la principal de las 100, peor que sin ella, así que **no se adoptó** (`FIRMA_NL = False`).

## 9. Limitaciones conocidas

1. **La comparación principal de las 100 sigue dando 0,735 a un lector de solo Lean** (CV dentro de las tripletas). Mejora frente a 0,88 sin imitación, pero queda lejos de 0,5. Fuera del lote de desarrollo y tras quitar las infieles defectuosas, solo 72 elegibles tienen imitación 2. Las 100 incluyen además 25 con imitación 1 y 3 con 0. El modelo congelado del lote de desarrollo es otro lector; su exactitud en las tripletas no se ha calculado a propósito.
2. **Huella cruzada NL–Lean**: C2 y E6 ponen un numeral ausente del NL (18 fieles, 60 infieles puras). El modelo de superficie del §5 no la ve, pero un probe sobre NL + Lean podría verla. Se reporta por combinación.
3. **Familias**: en la comparación principal, C 73, A 19, B 8.
4. Casos que la revisión debe mirar (P2):
   - la línea con `Erdos1097 weaker` tiene una C3 principal trivialmente falsa (etiqueta correcta);
   - los casos `Erdos358` (`parts.ii`, `one_le`), `Erdos5 banks_freiberg_maynard` y `Erdos657 straus` son dudosos según Fable (dependen de definiciones);
   - algunos NL de formal_conjectures son casi notas.
5. **Elaboración**: ninguna variante se ha elaborado en Lean. Los revisores piden elaborar O, F, X(O) y X(F) antes de certificar nada.
6. Tamaño de edición contado con expresión regular.

## 10. Qué debe aprobar Carlos

1. Este texto: tripleta, cuadrado, imitación, comparación principal única, McNemar exacto, criterio.
2. El modelo de superficie congelado y el análisis por δ (§5).
3. La revisión de `tripletas/muestra_tripletas_30.md` (P0, P1, P2).
4. Después: adaptar y correr la certificación (§6), registrar el SHA, marcas.

Las **reglas del generador** (E1–E7, imitación, selección) pasan por la revisión delegada Opus → Fable (ver la bitácora).
