# Nivel B — reglas del generador de pares mínimos (para aprobación de Carlos)

Borrador de Opus 1, 4 nov 2026 (~17 h, Bogotá). Basado en `probes/investigacion/caracterizacion_pares.md` (reglas A1–A3, B1–B4, C1–C3, D1–D5 de Sonnet B), con cambios que se explican abajo. **Nada está certificado ni registrado.** Ningún enunciado de este lote se ha elaborado con Lean.

- Código: `probes/nivel_b/generar.py` (determinista, semilla 20261104). Salida: `candidatos.jsonl` (9025 candidatos de 3429 enunciados de origen) y `resumen_generacion.json` (conteos, tamaños de edición, huellas, emparejamiento provisional y el SHA-256 del archivo).
- SHA-256 de `candidatos.jsonl` en el momento de escribir esto: ver `resumen_generacion.json` → `sha256_candidatos` (se recalcula en cada corrida; dos corridas seguidas dan el mismo).
- Muestra para revisión: `muestra_30.md` (`hacer_muestra.py`).

## 1. Fuentes y unidad

- **FormalMATH-Lite** (`datos/FormalMATH-Lite/FormalMATH_lite.json`, 425): NL = `refined_statement`, Lean = `autoformalization`.
- **formal_conjectures** en `prometeo_lean/aprobados/Corpus/corpus_v2.jsonl`: las 4083 filas cuyo `contexto_lean` termina en docstring; NL = el **último** `/-- … -/` (`rfind`). Solo las 3989 cuyas dependencias son `Mathlib` y/o `FormalConjecturesForMathlib` (lo que `corpus_compilar/corpus_lean` tiene compilado, para poder certificar). Todas tienen `verdad = verdadero` en el corpus.
- Filtros: NL de 30 a 3000 caracteres, Lean ≤ 2500 caracteres, enunciado de la forma `theorem nombre binders : conclusión := by [sorry]` (analizador propio). Quedan **4376 enunciados analizables** (37 descartados por longitud, 1 no analizable).
- **Unidad = enunciado de origen** (`id_origen`); el campo `grupo` es el hash del NL normalizado, igual que en `extraer.py`, así que todas las variantes de un origen caen en el mismo grupo en las particiones.
- Cada regla se aplica **como mucho una vez por origen**, en el **primer sitio aplicable** (hipótesis de izquierda a derecha y luego la conclusión, salvo que la regla diga otra cosa). La variante se construye con tramos `(inicio, fin, reemplazo)` sobre la cadena original: el resto del texto (formato, saltos de línea) queda idéntico.

## 2. Etiqueta y definiciones comunes

- **Etiqueta esperada** (respecto al NL original, suponiendo que el Lean original es adecuado): **adecuada** para D (mismo contenido), **inadecuada** para A, B y C (otro contenido).
- Lo que se compara es el **contenido** del enunciado, no su valor de verdad: dos teoremas verdaderos son equivalentes como proposiciones cerradas, pero `a < b` y `a ≤ b` dicen cosas distintas. Por eso la certificación (`certificar.py`, §6) compara las piezas editadas como fórmulas abiertas, no los teoremas.
- **Contexto monótono.** Las reglas que cambian una relación exigen: una sola relación de orden (`<`, `≤`, `>`, `≥`) en la fórmula, a profundidad 0 de paréntesis, sin `¬ → ↔ { } | λ fun ↦ if let have show match =>` en ninguna parte, sin `·`, y que la relación no sea la restricción de un ligador (`∀ n ≥ 1,`, `∃ x > 0,`). Esto deja la relación en posición positiva (bajo `∀ ∃ ∧ ∨ ∑ ∀ᶠ ∃ᶠ` como mucho), donde endurecerla hace el enunciado más fuerte y relajarla, más débil. *(Este filtro no estaba en la propuesta de Sonnet B; sin él, `∀ n ≥ 1, …` → `∀ n > 1, …` salía como «más fuerte» cuando es más débil.)*
- **Comparación pura**: `lhs op rhs` con una sola relación y lados sin ligadores, conectivos ni comas.
- **Hipótesis** = binder explícito `(h… : P)` cuyo nombre empieza por `h`/`H`; el resto son binders de datos.
- **Correlato en el NL** (obligatorio para A, B, C; registrado para D): algún numeral o identificador corto (≤ 3 caracteres, que no sea nombre de hipótesis) del fragmento editado aparece como palabra en el NL. Es un filtro **débil**: `x` aparece en casi cualquier NL que hable de `x`; no garantiza que el NL mencione la condición editada (p. ej. A1 en `FormalMATH_lite[116]` quita `hx : x ≠ 0`, que el NL no dice).
- **Tamaño de edición**: tokens de Qwen3-4B (`Qwen/Qwen3-4B@1cfa9a72`, solo el tokenizador, `HF_HUB_OFFLINE=1`) cambiados entre original y variante: suma, sobre los bloques no iguales de `difflib.SequenceMatcher(autojunk=False)` de las dos listas de ids, de max(quitados, puestos).
- **Huellas superficiales** (medidas en todo el lote; descriptivo, no entrena nada): si la variante añade un subíndice o prima, una `¬`, o un numeral que no está en el NL.

## 3. Reglas

Columnas: aplicables (= candidatos) en FormalMATH-Lite / formal_conjectures, mediana de tokens editados, cuántas entran en el emparejamiento provisional (§4).

| regla | FM | FC | total | tokens (mediana) | en pares provisionales | huella |
|---|---:|---:|---:|---:|---:|---|
| A1 quitar hipótesis | 71 | 212 | 283 | 8 | 32 | — |
| A2 endurecer conclusión | 20 | 267 | 287 | 1 | 46 | — |
| A3 relajar hipótesis | 76 | 181 | 257 | 1 | 162 | — |
| B1 añadir hipótesis `0 < v` | 38 | 11 | 49 | 9 | 0 | numeral fuera del NL 82 % |
| B2 relajar conclusión | 7 | 73 | 80 | 1 | 15 | — |
| B3 endurecer hipótesis | 18 | 237 | 255 | 1 | 175 | — |
| B4 quitar un conjunto | 13 | 25 | 38 | 13,5 | 12 | — |
| C1 ∀∃ → ∃∀ | 1 | 5 | 6 | 8 | 0 | — |
| C2 numeral N → N+1 | 364 | 1802 | 2166 | 1 | 216 | numeral fuera del NL 79 % |
| C3 invertir relación | 27 | 340 | 367 | 1 | 72 | — |
| D1 espejo (hip. primero) | 88 | 714 | 802 | 4 | 352 | — |
| D1c espejo en la conclusión | 23 | 314 | 337 | 6 | 41 | — |
| D2 `≠` ↔ `¬(=)` | 11 | 53 | 64 | 5 | **excluida** | `¬` 98 % |
| D3 renombrar ligada | 105 | 1288 | 1393 | 3 | **excluida** | subíndice 100 % |
| D4h reordenar hipótesis | 165 | 343 | 508 | 18 | 37 | — |
| D4c conmutar `∧` | 13 | 30 | 43 | 22 | 11 | — |
| D5 desplegar `Icc` | 3 | 13 | 16 | 9 | 0 | — |
| D6 renombrar hipótesis | 253 | 912 | 1165 | 1 | **excluida** | subíndice/prima 100 % |
| D7 `a ≤ b` → `¬(b < a)` | 84 | 510 | 594 | 7 | **excluida** | `¬` 100 % |
| D8 desplazar cota en ℕ/ℤ | 39 | 276 | 315 | 2 | 289 | numeral fuera del NL 36 % |

Totales: 3788 inadecuadas, 5237 adecuadas; 3429 orígenes con al menos un candidato.

Para cada regla: definición operativa; aplicabilidad; ejemplo real (el primero tras ordenar por FormalMATH primero, con correlato, más corto); etiqueta; dirección trivial; riesgos.

### A — más fuertes (inadecuadas: afirman más de lo que dice el NL)

**A1 — Quitar una hipótesis.** Elimina un binder de hipótesis atómico (comparación pura con `< ≤ > ≥ ≠`) cuyo nombre no aparece en ningún otro sitio del enunciado; exige ≥ 3 binders. Se quita también el espacio (o la línea) que lo precede.
- Ejemplo (`FormalMATH_lite[116]`, 8 tokens). NL: «If $x \%$ of 60 is 12, what is $15 \%$ of $x$? Prove that the answer is: 3». Original: `theorem omni_theorem_2816 (x : ℝ) (hx : x ≠ 0) (h : (x / 100) * 60 = 12) : (15 / 100) * x = 3`. Variante: sin `(hx : x ≠ 0)`.
- Etiqueta: inadecuada (cuantifica sobre más casos de los que permite el NL). Dirección trivial: variante ⇒ original.
- Riesgos: **equivalencia accidental** si la hipótesis es redundante — es justo el caso del ejemplo: `h` ya implica `x ≠ 0`, así que la variante es equivalente; el NL tampoco menciona `x ≠ 0` (el correlato pasó por la letra `x`). La certificación de nivel 2 (§6) lo detecta: no existe testigo que cumpla `h` con `x = 0`, y `omega`/`linarith`/`simp_all` pueden probar la redundancia. Puede volver falsa la variante (no importa para fidelidad; ver §5).

**A2 — Endurecer la conclusión** (`≤` → `<`, `≥` → `>`), con contexto monótono.
- Ejemplo (`FormalMATH_lite[156]`, 1 token). NL: «Suppose positive numbers a, b, c satisfy (1+a)(1+b)(1+c)=8. Prove that abc ⩽ 1.» Original `… : a * b * c ≤ 1`; variante `… : a * b * c < 1`.
- Inadecuada; dirección trivial variante ⇒ original (`le_of_lt`). Riesgos: si la cota nunca se alcanza, la variante es verdadera y sigue siendo inadecuada (afirma otra cosa); si se alcanza (aquí `a=b=c=1`), la variante es falsa.

**A3 — Relajar una hipótesis** (`<` → `≤`, `>` → `≥`), hipótesis con una sola relación en contexto monótono.
- Ejemplo (`FormalMATH_lite[18]`, 1 token). NL: «Let n be a positive integer. Prove that gcd(n!+1,(n+1)!+1)=1.» `(hn : n > 0)` → `(hn : n ≥ 0)`.
- Inadecuada; variante ⇒ original. Riesgos: en ℕ, `n ≥ 0` es vacuo (equivale a A1); equivalencia accidental si las demás hipótesis obligan la estricta (`FormalMATH_lite[342]`): lo detecta el nivel 2.

### B — más débiles (inadecuadas: afirman menos de lo que dice el NL)

**B1 — Añadir `(h<v>_pos : 0 < v)`** al final de los binders, para una variable `v : ℝ/ℤ/ℚ` explícita que aparece en el NL, sin hipótesis de signo previa sobre `v`, y solo si el NL no contiene palabras de signo/orden («positive», «nonnegative», «natural», `\gt`, `<`, `≠`…). Versión automática y restringida de la B1 manual de Sonnet B.
- Ejemplo (`FormalMATH_lite[211]`, 9 tokens). NL: «Proof: arcsin x + arccos x = π/2.» `(x : ℝ) : arcsin x + arccos x = π / 2` → `(x : ℝ) (hx_pos : 0 < x) : …`.
- Inadecuada; original ⇒ variante. Riesgos: hipótesis inconsistente con las demás (variante vacía); simetría (WLOG). Huella: el numeral `0` no está en el NL (82 %). No entra en pares provisionales (sus 9 tokens no encuentran fiel del mismo intervalo en su origen).

**B2 — Relajar la conclusión** (`<` → `≤`, `>` → `≥`). Ejemplo (`FormalMATH_lite[374]`): `a * b * c > a + b + c - 2` → `≥`. Original ⇒ variante. Riesgo: si el caso de igualdad es imposible bajo las hipótesis, la diferencia de contenido es pequeña, pero existe como fórmula (testigo de nivel 1).

**B3 — Endurecer una hipótesis** (`≤` → `<`, `≥` → `>`). Ejemplo (`FormalMATH_lite[16]`): NL «k ⩾ 2»; `(hk : 2 ≤ k)` → `(hk : 2 < k)`. Original ⇒ variante. Riesgo (de Sonnet B): en ℕ/ℤ, `2 < k` es `3 ≤ k`, que excluye `k = 2`: sigue siendo inadecuada. Es el contraste natural de D8.

**B4 — Quitar el segundo conjunto** de una conclusión `A ∧ B` (un único `∧` de nivel 0, sin cuantificadores ni comas). Ejemplo (`FormalMATH_lite[184]`, 13 tokens): `(cosh x + sinh x = exp x) ∧ (cosh x - sinh x = exp (-x))` → `(cosh x + sinh x = exp x)`. Original ⇒ variante. Riesgo: `B` consecuencia de `A` (equivalencia).

### C — otro teorema (inadecuadas)

**C1 — `∀ x, ∃ y, P` → `∃ y, ∀ x, P`** (tipos independientes; `x` aparece en `P`). Ejemplo (`FormalMATH_lite[3]`): `∀ N, ∃ n, n > N ∧ …` → `∃ n, ∀ N, n > N ∧ …`. Lógicamente es más fuerte (variante ⇒ original), como notó Sonnet B. Solo 6 casos; no entra en pares.

**C2 — Numeral `N → N+1`** (N ≥ 2, el numeral aparece en el NL, no es exponente ni índice de `Fin`); primero en hipótesis, luego en la conclusión. Ejemplo (`FormalMATH_lite[361]`): NL «What is 110 % of 500? … 550»; `(110 / 100 : ℝ) * 500 = 550` → `(111 / 100 : ℝ) …`. Dirección trivial: ninguna en general (en `2 ≤ q` → `3 ≤ q` sí hay una; la certificación prueba la que haya). Riesgos: (i) la variante suele ser trivialmente falsa y detectable por cálculo (señal de «verdad», no de fidelidad: §5); (ii) **huella cruzada**: el numeral nuevo no está en el NL en el 79 % de los casos. Un comparador de cadenas NL–Lean la ve; el probe solo-Lean no. Por eso hay un control de superficie cruzada (regla_borrador.md) y D8 añade numerales ausentes del NL del lado fiel (36 %).

**C3 — Invertir la relación** (`≤` ↔ `≥`, `<` ↔ `>`) en la conclusión, sin intercambiar lados. Ejemplo (`FormalMATH_lite[374]`): `abc > a+b+c−2` → `abc < a+b+c−2`. Sin dirección trivial.

### D — reescrituras fieles (adecuadas: mismo contenido)

**D1 — Espejo** de una comparación pura: `a < b` → `b > a`, `a ≤ b` → `b ≥ a` (y al revés); primera hipótesis aplicable, si no, la conclusión. Ejemplo (`FormalMATH_lite[18]`, 4 tokens): `(hn : n > 0)` → `(hn : 0 < n)`. Equivalencia: `>`/`≥` son notación reducible (`Iff.rfl`). Riesgo: coerciones distintas (`(n : ℝ) > 0`); la certificación lo comprueba. **D1c** es la misma regla solo en la conclusión (ejemplo `FormalMATH_lite[374]`, 12 tokens), para emparejar con A2/B2/C3.

**D2 — `a ≠ b` ↔ `¬(a = b)`** (hipótesis o conclusión). `Iff.rfl`. **Excluida de los pares**: añade `¬` en el 98 %.

**D3 — Renombrar una variable ligada** de la conclusión (`x` → `x₁`, nombre nuevo fresco en el enunciado y el contexto; ≥ 2 apariciones). α-equivalencia (`Iff.rfl`). Ejemplo (`FormalMATH_lite[12]`): `¬ ∃ x y : ℤ, x^3 + y^4 = 7` → `¬ ∃ x₁ y : ℤ, x₁^3 + y^4 = 7`. **Excluida de los pares**: subíndice nuevo en el 100 %.

**D4h — Intercambiar dos hipótesis adyacentes** independientes. Ejemplo (`FormalMATH_lite[108]`, 16 tokens): `(hx : x = 3) (hy : y = 4)` → `(hy : y = 4) (hx : x = 3)`. Equivalencia lógica (no definicional): `intro/apply/assumption`. **D4c — conmutar el único `∧`** de nivel 0 de la conclusión (`FormalMATH_lite[184]`, 24 tokens); `and_comm`. Ediciones grandes: emparejan con A1/B4.

**D5 — Desplegar `Icc`**: `x ∈ Set.Icc a b` → `a ≤ x ∧ x ≤ b` (hipótesis) o `∀ x ∈ Icc a b,` → `∀ x, a ≤ x ∧ x ≤ b →` (conclusión). Ejemplo `FormalMATH_lite[282]`. `Set.mem_Icc` / `Finset.mem_Icc`. Riesgo: índice de `∑` (excluido por el patrón). Solo 16.

**D6 — Renombrar una hipótesis** (`h` → `h₀`, o `h₀` → `h₀'`) en todo el enunciado. `Iff.rfl`. 1 token. **Excluida de los pares**: subíndice/prima nuevo en el 100 %.

**D7 — Negación de la relación opuesta**: `a ≤ b` → `¬(b < a)`, `a < b` → `¬(b ≤ a)` (y con `≥`, `>`), solo con evidencia de orden lineal (todas las variables del enunciado que aparecen son de tipo ℕ/ℤ/ℚ/ℝ). Ejemplo (`FormalMATH_lite[18]`): `(hn : n > 0)` → `(hn : ¬(n ≤ 0))`. `not_le`/`not_lt`. **Excluida de los pares**: `¬` nueva en el 100 %.

**D8 — Desplazar la cota en ℕ/ℤ** (nueva): `N ≤ x` → `N−1 < x`, `N < x` → `N+1 ≤ x`, `x ≤ N` → `x < N+1`, `x < N` → `x ≤ N−1` (y los simétricos con `≥`, `>`), si el otro lado es aritmética simple (`+ * -`) de variables del enunciado de tipo ℕ/ℤ y nunca si el numeral nuevo sería negativo. Ejemplos de la corrida: `2 ≤ u` → `1 < u`; `0 < k` → `1 ≤ k`; `n ≥ 2` → `n > 1`. Equivalencia: `omega`. 2 tokens. Es el **mejor control** para B3 y C2: misma posición, mismo tipo de edición (relación + numeral), mismo tamaño; solo cambia si el contenido se conserva (`2 ≤ k` → `1 < k` fiel; `2 ≤ k` → `2 < k` infiel; `2 ≤ k` → `3 ≤ k` infiel).

## 4. Emparejamiento por tamaño de edición (para que «hubo un cambio» no sea la señal)

Todas las filas del contraste clave están editadas: el probe compara **infiel-editada frente a fiel-editada** del **mismo** origen, con el mismo NL. Procedimiento (`generar.emparejar`, semilla fija; se rehace después de certificar, solo con candidatos certificados):

1. Intervalos de tokens editados: **1–4, 5–8, 9–14, 15–24, 25+**. Una infiel solo se empareja con una fiel **del mismo origen y del mismo intervalo**.
2. Entre las fieles libres del intervalo se prefiere, por orden: (a) que editen la misma clase de objeto (relación, numeral, hipótesis entera, conjunción; D8 cuenta como relación y numeral), (b) la misma zona (hipótesis/conclusión), (c) el menor |Δ tokens|, (d) sorteo con semilla.
3. Infieles en orden aleatorio, primero una por familia (A, B, C); como mucho **2 pares por origen**; cada candidato en un solo par.
4. **D2, D3, D6, D7 no entran en los pares** (huella superficial alineada con la etiqueta, medida en §3). Se generan y certifican igual (sirven para un análisis secundario de huellas, si Carlos lo quiere).

Provisional (antes de certificar): **730 pares en 472 orígenes** (A 240, B 202, C 288; FormalMATH 124, FC 606); misma zona 578, misma clase de objeto 590; combinaciones más frecuentes C2~D1 115, B3~D8 101, A3~D1 92, C2~D8 89, B3~D1 74, A3~D8 70. Mismo intervalo en el 100 % (por construcción), pero **asimetría dentro del intervalo 1–4**: infieles media 1,9 tokens (mediana 1), fieles 4,1 (mediana 4), |Δ| medio 2,3. Con intervalos más finos (1–2, 3–4, …) quedaban 324 pares, casi todos con D8. El análisis reporta aparte los pares con |Δ| ≤ 1 y la pendiente del Δpuntaje sobre Δtokens (regla_borrador.md).

## 5. Control «fidelidad ≠ verdad»

Todos los originales se suponen verdaderos (formal_conjectures: `verdad = verdadero` en el corpus; FormalMATH: supuesto). Entonces:
- **B** (más débil) con la dirección original ⇒ variante probada: la variante **es verdadera** y es inadecuada. Si el probe separa los pares con infiel B, no está detectando falsedad.
- **A/C en la conclusión con testigo de nivel 2**: la variante está **refutada** (falsa). Estos pares mezclan infidelidad con falsedad.
- **D**: misma verdad que el original.
`certificar.py` registra `verdad_variante` por candidato; el análisis compara la AUROC pareada en ambos subconjuntos (y P(Yes), que sí podría seguir a la verdad).

## 6. Certificación (preparada, sin correr): `certificar.py`

Un archivo `.lean` por origen (cabecera + contexto de formal_conjectures sin el docstring final + un `example` por intento; un intento vale si su `example` no da error). Nunca se intenta probar una variante como teorema.
- **D**: equivalencia local `example <datos> : F_O ↔ F_V` (F = hipótesis o conclusión editada) o global `P_O ↔ P_V`, con tácticas estructurales: `Iff.rfl`, `and_comm`, `not_lt.symm`, `not_le.symm`, `simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]`, `omega`, `constructor <;> intro _ <;> omega/linarith`, `intro/apply/assumption`. Ninguna prueba el teorema en sí.
- **A/B/C**: (i) dirección trivial (`intro/apply/assumption/le_of_lt/And.left/omega/linarith`; `aesop` se registra aparte); (ii) **accidental** (solo hipótesis): `example <datos> <demás hipótesis> : F_O ↔ F_V` con `omega`, `linarith`, `nlinarith`, `positivity`, `simp_all`; si cierra → «equivalente_accidental», se descarta. No toca la conclusión, así que no usa la verdad del teorema. (iii) **testigo de nivel 2**: valores concretos que cumplen las demás hipótesis y separan F_O de F_V (hipótesis), o que cumplen todas las hipótesis y refutan la conclusión de V (A/C en la conclusión); (iv) **testigo de nivel 1**: valores que separan F_O de F_V como fórmulas abiertas. Testigos solo con variables ℕ/ℤ/ℚ/ℝ, rejilla pequeña (numerales del fragmento ±1 primero; ≤ 32 combinaciones), `⟨…, by norm_num⟩`. (v) `plausible` (existe en el Mathlib del toolchain: `Mathlib/Tactic/Common.lean` importa `Plausible`; `slim_check` ya no está) como buscador de contraejemplos; sus valores se comprueban con `norm_num` en una segunda pasada.
- **Qué cuenta como certificado** para el análisis: fiel «equivalente»; infiel «no_equivalente» con **nivel 2 si la edición es de hipótesis** (el nivel 1 de una hipótesis atómica es casi automático y no descarta redundancias, como en el ejemplo de A1) y **nivel ≥ 1 si es de la conclusión** (bajo hipótesis no se puede pedir más sin confundir con la verdad: para una B de un teorema verdadero, `C_O ↔ C_V` vale bajo las hipótesis). «sin_decidir» y «no_elabora» se cuentan aparte.
- Estimación de pares que sobrevivirán (heurística sin Lean: testigos posibles solo con tipos numéricos): **~450 pares en ~320 orígenes**, probablemente menos (hipótesis con funciones definidas en formal_conjectures que `norm_num` no evalúa).
- Tiempo estimado (no medido): ~3,2 h-CPU para los 472 orígenes con par provisional (import de Mathlib 2,8 s en caliente, medido por `compilar_v2.py`; ~2 s de contexto en formal_conjectures; ~0,1 s por `example`): **~1 h con 4 procesos, ~40 min con 6**, ~30 min con 8 (con 8 la memoria puede apretar con otros trabajos). Todo el lote (`--todos`, 3429 orígenes): ~12 h-CPU, ~3,5 h con 4.

## 7. Qué debe aprobar Carlos

1. Las reglas (§3), incluidas las dos nuevas (D8, B1 automática) y los cambios (filtro de contexto monótono; A1 solo hipótesis atómicas; reglas con huella fuera de los pares).
2. El emparejamiento (§4) y el criterio de certificado (§6).
3. Revisión de `muestra_30.md`. Luego, registro de `candidatos.jsonl` con SHA-256 en `prometeo_lean/aprobados/` + línea en `FECHA`, y las marcas `APROBADO_reglas` (con el SHA), `APROBADO_muestra`, `APROBADO_regla_decision`, `APROBADO_lean` en `probes/nivel_b/`.

## Cambios del revisor (Fable, 2026-11-04)

Revisión independiente sin Lean, sin modelos y sin GPU; solo lectura de `candidatos.jsonl` con Python en CPU (`generar.emparejar` reproducido con la misma semilla: 730 pares). Lo que sigue corrige o matiza afirmaciones de este documento; las recomendaciones completas están en `probes/revision_fable_2026-11-04.md`.

1. **§2 y §3, «huellas superficiales»: la tabla dice «—» para D1 y D8, pero las dos dejan una huella alineada con la etiqueta, medible con solo el Lean.** Sobre los 730 pares provisionales, una regresión logística con unigramas y bigramas del **Lean variante solamente** (CV de 5 pliegues agrupada por origen, sin activaciones) alcanza una **AUROC pareada ≈ 0,85** (0,91 en los 352 pares con fiel D1; 0,83 con D8; 0,79 con D1c; 0,74 con D4h; 0,77 si se enmascaran `< ≤ > ≥`). Causas visibles: (i) D1/D1c **introduce** `>`/`≥` en 362 de 393 pares (los originales siguen el estilo Mathlib `<`/`≤`); en los fragmentos variante de los pares, `≥` aparece 227 veces del lado fiel y 72 del infiel, `>` 162 frente a 28; (ii) D8 produce casi siempre `1 ≤ x`, `0 < x`, `1 < x` (numerales 0 y 1 del lado fiel), mientras B3 produce `2 < x`, `3 < x` (el numeral 3 aparece en 170 fragmentos infieles y 55 fieles). La huella es la **identidad de la regla**, legible en la forma del Lean. La prueba central (completo − solo_lean) la resta, pero (a) deja a solo_lean cerca del techo y comprime la diferencia, y (b) los pares no son «mínimos» en el sentido que promete el nombre. La corrección natural, que no apliqué porque cambia el diseño: **componer** la reescritura fiel con la edición infiel (par = (D∘X, D): los dos miembros llevan la misma firma de D y solo difieren en X), o al menos aplicar D1 solo en la dirección que quita `>`/`≥` (quedan 69 candidatos; el emparejamiento se desploma a 375 pares, casi todos D8, con huella 0,84 todavía) y exigir, como compuerta antes de extraer activaciones, que esta línea base de superficie sobre los pares certificados no pase de un umbral fijado (propongo 0,70).
2. **§1, fuente formal_conjectures: el NL extraído contenía código Lean en algunos orígenes.** `doc_nl` tomaba el último `/--` y cortaba en el `-/` final, pero cuando el contexto termina en un comentario corriente `/- … -/` posterior al docstring, el «NL» mezclaba el docstring con `abbrev`, `instance`, etc. (caso 25 de `muestra_30.md`). Corregido en `generar.py` (`doc_nl` descarta el origen si el cuerpo contiene `-/`). **Hay que regenerar `candidatos.jsonl`; cambia su SHA-256** y, con él, el que iría en `APROBADO_reglas`. Ningún otro cambio de lógica.
3. **§2, «correlato en el NL»: es más débil de lo que parece para las reglas de relación.** En los pares provisionales, el 15 % de A3 (24/162) y de B3 (27/175) no tiene en el NL ninguna palabra ni símbolo de orden («at least», «positive», `\ge`, `<`, …); el correlato pasó por una letra. Ejemplo: caso 16 de la muestra (`0 < n` → `0 ≤ n` con un NL que no restringe `n`). Propuesta: para A2, A3, B2, B3, C3 exigir correlato de orden; con ese filtro, NL sin restos de Lean y NL ≥ 60 caracteres sobreviven 609 de los 730 pares (403 orígenes) antes de certificar.
4. **§1, premisa «suponiendo que el Lean original es adecuado»: no siempre se cumple.** Caso 22 de la muestra: el docstring dice `3 ≤ k ≤ 203` y el Lean `k ≤ 300` (`verdad = verdadero` en el corpus). Cuando el original ya es infiel, la etiqueta «adecuada» de la D es falsa respecto al NL y la B3 compara dos infieles. La revisión de la muestra debería preguntar también «¿el original es adecuado al NL?».
5. **§1, unidad y particiones: 220 de los 472 orígenes con par comparten archivo fuente con otro origen** (p. ej. `OpenQuantumProblems/35` aporta 12, `Arxiv/0805.3777/TensorRank` 11, `ErdosProblems/504` 6). Los pliegues agrupados por NL dejan en entrenamiento y prueba enunciados casi duplicados (`a_2`, `a_3`, `a_5` de la misma sucesión OEIS). Propuesta: agrupar por archivo (`OEIS/24356`, `ErdosProblems/504`, …) y reportar el bootstrap por archivo como sensibilidad.
6. **§2, «NL de 30 a 3000 caracteres»**: 20 pares tienen NL < 60 caracteres y 8 tienen un NL que es una nota («The case k = 2 is the theorem of Nash-Williams», «Value of the sequence `a` at 2») y no un enunciado. Son ruido que diluye la ventaja de «completo» (sesgo conservador), pero conviene filtrarlos.
7. **§5, control fidelidad ≠ verdad**: los pares con infiel B son casi todos ediciones de hipótesis y los A/C refutados son ediciones de conclusión; la comparación mezcla verdad con zona. Reportar también dentro de cada zona.
8. **§6, testigos**: la rejilla ordena las combinaciones por índice y antepone los numerales del fragmento (54, 53, 55, 56 en el caso 4), así que un testigo como (a, b) = (1, 7) queda fuera de las 32 combinaciones; `plausible` es el único respaldo. No lo cambié; es una elección, no un error.
9. **§6, `extraer_pares.py`** reutiliza el desarreglo de `probes/extraer.py` sin la reparación por intercambios del Nivel C; con grupos de 3 a 5 filas por origen el rechazo debería bastar, pero si aborta («No encontré desarreglo») la causa es esa.

## Cambios del revisor — segunda pasada (Fable, 2026-11-04, ~19 h): lote v2 aplicado

Carlos pidió aplicar las recomendaciones. **Nada aprobado, nada lanzado, sin Lean ni modelos.** `candidatos.jsonl` (v1) queda intacto como histórico; el lote nuevo es `candidatos_v2.jsonl`.

- **SHA-256.** v1 `candidatos.jsonl`: `83d13a0c22de666f951ec43a60492cc4ceb6d9699de9b8cea1beee63b8281246`. v2 `candidatos_v2.jsonl`: `f66e114cf33fed927ba8fa9b53092b0a615d2752a64d8a99b78a571663e8cecd` (tokenizador Qwen3-4B, `generar.py --v2`, semilla 20261104; dos corridas dan el mismo SHA). Resumen: `resumen_generacion_v2.json`. `lanzar.sh` usa v2 y exige su SHA en `APROBADO_reglas`.

### Qué cambia en v2 (`generar.py`, bloque «Versión 2»)
1. **NL que sea un enunciado**: ≥ 60 caracteres, sin restos de Lean (`-/`, `/-`, `abbrev`, `instance`, `:=`, `namespace`, `def`/`theorem`/`lemma` al inicio de línea) y sin notas («The case k = 2 is…», «Value of the sequence…», «See […]», «Proved by…», «Reference: […]»). Descarta 857 orígenes de 4376; quedan **3415 analizables**. `doc_nl` corregido (primera pasada).
2. **Correlato de orden** para A2/A3/B2/B3/C3: el NL debe contener una palabra o símbolo de orden (`ORDEN_NL`), además del correlato de letra o numeral de v1.
3. **Sin ediciones triviales en ℕ**: se descartan las variantes que dejan `0 ≤ n`, `n ≥ 0` (vacuas) o `n < 0`, `0 > n` (imposibles) con `n : ℕ` (173 candidatos, 56 de A3 puro). Se ven sin leer el NL.
4. **Composición X∘D**: cada edición infiel X se aplica sobre la variante fiel D del mismo origen; el par es **(X∘D, D)**: los dos miembros llevan la misma firma de D y difieren solo en X. Bases: D1/D1c/D8 para A2/A3/B2/B3/C2/C3 y A1/B1; D4h para A1/B1; D4c para B4. X no tiene que ser aplicable al original: así `2 ≤ k` da B3∘D1 = `k > 2` **y** A3∘D8 = `1 ≤ k`, y la estrictez deja de predecir la etiqueta por construcción. Las X puras y C1 se generan y certifican pero **no entran en los pares** (`EXCLUIR_DE_PARES_V2`); D1/D1c/D8/D4h/D4c/D5 puras solo emparejan con sus compuestas. Los candidatos compuestos llevan `lean_base`, `base_fiel`, tramos relativos a la base y `tokens_editados_vs_base`. `certificar.piezas` acepta reglas «X∘D» (A1 por texto de la hipótesis quitada, por si la base es D4h).
5. **`archivo`** en cada candidato (`OEIS/24356`, `ErdosProblems/504`, `FormalMATH_lite[i]`), para agrupar pliegues por archivo.

### Conteos v2
- Candidatos: **10 658** (5922 inadecuadas, 4736 adecuadas). Puras: A1 270, A2 223, A3 163, B1 47, B2 70, B3 212, B4 32, C1 5, C2 1726, C3 293, D1 679, D1c 243, D2 54, D3 1320, D4c 36, D4h 484, D5 15, D6 1072, D7 541, D8 292. Compuestas (las más frecuentes): C2∘D1 361, A1∘D1 257, C3∘D1 235, A1∘D4h 212, B3∘D1 203, C3∘D1c 200, A2∘D1 190, A2∘D1c 169, C2∘D8 152, A3∘D1 148, A1∘D8 132, A3∘D8 116, B3∘D8 115, C2∘D1c 111.
- **Emparejamiento provisional: 1111 pares (todos compuestos) en 618 orígenes y 431 archivos** (FormalMATH 198, formal_conjectures 913); por familia infiel A 488, B 235, C 388; por base fiel D1 536, D8 226, D1c 188, D4h 134, D4c 27. |Δ tokens| medio respecto al original 2,1 (la infiel lleva la edición de D más la de X). v1 tenía 730 pares en 472 orígenes.

### Compuerta de superficie (`compuerta_superficie.py`; JSON en `compuerta_superficie_provisional.json`)
Regresión logística sobre unigramas y bigramas del Lean variante, CV de 5 pliegues agrupada por archivo, AUROC pareada por origen:
- **v1: 0,852.** **v2: 0,771** (operadores `< ≤ > ≥` enmascarados: 0,658). Por base fiel: D8 0,64, D1 0,79, D4h 0,82, D1c 0,83, D4c 0,93. Por familia infiel: A 0,79, B 0,74, C 0,74.
- **No pasa el criterio estricto (≤ 0,70).** Lo intenté además con (i) equilibrar la estrictez del operador por estrato (base × zona): 946 pares, 0,779, no ayuda; (ii) solo pares de relación equilibrados: 441 pares, 0,731, y con operadores enmascarados **exactamente 0,500**; (iii) solo bases D8/D4h/D4c: 387 pares, 0,749; (iv) **solo base D8: 226 pares, 0,701** (exceso sobre tipicidad 0,064).
- **Por qué no baja más**: lo que queda no es la firma de la regla (ya está compartida por los dos miembros) sino la **convención de Mathlib**: los originales son casi siempre `0 < n` o `2 ≤ k`; una edición infiel produce la forma atípica (`k > 2`, `n ≥ 1`…) y un lector que solo ve el Lean aprende «forma atípica = infiel». Eso es inherente a editar enunciados típicos y no se elimina por construcción sin hacer atípicas también las fieles (D7, D2…, excluidas por la huella `¬`). La prueba (ii) lo muestra: con el operador enmascarado no queda nada (0,500). La línea base no supervisada de tipicidad que implementé (bigramas raros respecto a los originales, sin etiquetas) captura poco de esto (0,57), así que el «exceso» de 0,20 sobreestima la firma de regla.
- **Decisión para Carlos** (`--criterio` de la compuerta; `CRITERIO=` en `lanzar.sh`): (a) lote v2 completo con el criterio «firma» y la explicación anterior en el informe (la prueba central resta solo_lean, así que la convención no infla la diferencia, pero solo_lean parte alto: ~0,77 por superficie); o (b) lote restringido a la base D8 (`generar.py --v2 --bases D8` → `candidatos_v2_D8.jsonl`), que roza el criterio estricto (0,70) con 226 pares provisionales (menos de los 400 «confirmatorios», probablemente ~150 tras certificar). Mi recomendación: (a) para el análisis principal, y reportar el subconjunto D8 como secundario preespecificado.

### Pendiente de Carlos
Revisar `muestra_30_v2.md` (30 casos, 29 reglas, solo candidatos con par; pregunta P0: ¿el original es fiel al NL?); elegir el criterio de la compuerta; registrar el SHA de v2 en `prometeo_lean/aprobados/` + `FECHA` y crear las marcas; decidir `--todos` en la certificación.

## Reglas fieles nuevas para tripletas (E1–E7) — 4 nov 2026, noche

Borrador de la sesión lateral de tripletas, según la opción «b» que eligió Carlos (~23:3x). Código: `tripletas/reglas_fieles_nuevas.py`, que importa `generar.py` sin editarlo; autoprueba con `python -I tripletas/reglas_fieles_nuevas.py`. Uso: solo como fieles atípicas F de las tripletas (`regla_v2_tripletas.md`). **No entran en los lotes v1–v3.** Nada certificado.

**Por qué.** Fuera del lote de desarrollo no queda ningún enunciado en el que D1, D1c, D8 o D7 den una fiel de operador, porque esas reglas solo miran comparaciones puras a nivel 0 de una hipótesis o de la conclusión. Las E extienden la misma idea a **átomos de relación en cualquier posición**: bajo `∀`/`∃`/`∀ᶠ`, dentro de `∧`/`∨`/`→`, en un conjunto por comprensión. También añaden simetrías.

**Átomo.** Es `lhs op rhs` con op ∈ {`<` `≤` `>` `≥` `=` `≠`} rodeado de espacios. Se delimita por el paréntesis que abre o cierra su grupo, o por `, ∧ ∨ → ↔ ¬ | :` al mismo nivel. Además:
- los lados son términos puros (`generar.termino_puro`) sin `∈ ∉ ⊆ ⊂ ≡ ∣ · ∘` y sin palabras `then`, `else`, `in`, `at`, `if`, `from`, `with`, `by`;
- el átomo está fuera de comentarios;
- si el delimitador izquierdo es una coma, la coma pertenece a un `∀`/`∃`, nunca a `∑ ∏ ∫ ⋃ ⋂ ⨆ ⨅`. Así `∑ i in s, f i ≤ 5` no se toca, porque es `(∑ …) ≤ 5`.

Como cada regla reemplaza una subfórmula por otra **equivalente como fórmula abierta**, vale en cualquier contexto: no hace falta monotonía.

| regla | edición | equivalencia prevista | condiciones |
|---|---|---|---|
| E1 | `a = b` → `b = a` | `eq_comm` | átomo `=` |
| E2 | `a ≠ b` → `b ≠ a` | `ne_comm` | átomo `≠` |
| E3 | `(h : A ∧ B)` → `(h : B ∧ A)` | `and_comm` | único `∧` de nivel 0 de una hipótesis, sin cuantificadores, comas ni `∨` (D4c cubre la conclusión) |
| E4 | `A ∨ B` → `B ∨ A` | `or_comm` | único `∨` de nivel 0 de una hipótesis o de la conclusión, sin cuantificadores, comas ni `∧` |
| E5 | `a < b` → `b > a`, `a ≤ b` → `b ≥ a` (y al revés) | `Iff.rfl` (`>`/`≥` son notación) | cualquier átomo de orden |
| E6 | `N ≤ t` → `N−1 < t`, `N < t` → `N+1 ≤ t`, `t ≤ N` → `t < N+1`, `t < N` → `t ≤ N−1` (y simétricos) | `omega` | `t` de tipo ℕ o ℤ **comprobado**; ningún numeral negativo |
| E7 | `0 < t` / `t > 0` → `t ≠ 0`, `t ≠ 0` → `0 < t` | `Nat.pos_iff_ne_zero` (`omega`) | `t` de tipo **ℕ** comprobado (en ℤ no vale) |

**Tipo de `t` (E6/E7)** (`tipo_discreto`). `t` es aritmética `+ − * / %` (y `^`, cuyo tipo es el de la base) de átomos que pueden ser:
- numerales;
- variables declaradas en los binders, de tipo ℕ/ℤ;
- variables ligadas **con tipo explícito** (`∀ n : ℕ,`, `∃ (a b : ℤ),`);
- aplicaciones `f x` con `f` de codominio ℕ/ℤ (binder o `def`/`variable` del contexto);
- proyecciones de valor ℕ (`.card`, `.ncard`, `.natAbs`, `Nat.totient` …);
- una adscripción explícita `(e : ℤ)`.

Una variable ligada sin tipo, `↑` o `!` dejan el tipo desconocido, y entonces la regla **no** se aplica.

**Huellas** (medidas como en v2 sobre los 1009 orígenes elegibles fuera del lote de desarrollo; `resumen_tripletas_100.json` → `reglas_E_en_origenes_no_excluidos`):
- ninguna regla E añade subíndices, primas ni `¬`;
- E5 añade `>`/`≥` en el 87 %;
- E7 añade `≠` en el 89 %;
- E6 añade un numeral ausente del NL en el 34 %;
- E1–E4: ninguna de las huellas medidas.

Por eso la selección de tripletas exige **imitación**: la edición fiel y la infiel deben quitar y poner las mismas clases de token (regla_v2_tripletas.md §1). Así la huella de E5 queda en los dos lados: en las 100 tripletas, `>`/`≥` nuevo aparece en 48 fieles y en 48 infieles puras.

**Revisión (Opus → Fable, 4–5 nov 2026; aprobación delegada de las reglas del generador): «aprobar con correcciones», aplicadas.** En `reglas_fieles_nuevas.py`:
- **O1**: `|` es delimitador solo si es la barra de un conjunto por comprensión; se descartan los lados que empiezan o terminan en operador o que tienen un número impar de `|`.
- **O2**: un recolector único de variables ligadas (todas las formas de ligador y la comprensión). Una ligada se tipa solo si se liga una vez y con tipo explícito, y si coincide con el binder del teorema del mismo nombre.
- **O3**: `choose` sale de `FUNC_N`, y se rechazan los prefijos `ENat.`, `PartENat.`, `Cardinal.`, `Classical.` y `Exists.`.
- **O4**: el dueño de la coma ya no salta otras comas, y `∮ ⨁ ∐ Σ Π` cuentan como ligadores grandes.
- **O5**: en `^`, el exponente tiene que ser ℕ o un numeral.
- **O6**: no se editan hipótesis cuyo nombre se usa en otra parte del enunciado.

La autoprueba tiene ahora 41 casos, incluidos los adversariales de los dos informes. Los filtros de infieles (O7–O10) están en `tripletas/filtros_infieles.py` y se describen en `regla_v2_tripletas.md` §1. La huella de E5 (87 %) se midió sobre los candidatos, no sobre la salida.

**Pendiente antes de certificar**: `certificar.py` no conoce E1–E7. Para un átomo bajo un ligador, la pieza tiene variables ligadas libres: hay que certificarla cuantificada (`∀ n, (P n ↔ P' n)`) o comparar el enunciado entero (`forall_congr'`).
