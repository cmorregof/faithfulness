# Nivel C: informe (ProofNetVerif, Qwen3-4B) — 6 nov 2026

*Preliminar, sin revisión por pares.*
- La regla de decisión (`regla_borrador.md`, SHA-256 `d6dadc92…`) la aprobó Carlos el 4 nov a las 22:06, con hora fijada a las 22:29. Se aprobó antes de calcular cualquier métrica con etiquetas.
- El §10 de la regla exigía una segunda implementación independiente que reprodujera C1. **Esa condición se cumplió.**

## Pregunta
**C1:** con etiquetas humanas de otra fuente (ProofNetVerif), sin juez LLM y con negativos naturales, ¿las activaciones de Qwen3-4B separan formalizaciones Lean adecuadas de inadecuadas **más allá del Lean solo**?

**C2:** ¿la dirección aprendida en CriticLeanBench transfiere a ProofNetVerif?

## Datos y procedimiento
- **Datos:** `PAug/ProofNetVerif@91183e5b` (MIT), valid + test.
  - 3752 pares (NL, Lean); 1142 adecuados (30,4 %).
  - 361 enunciados, agrupados por el NL normalizado: 217 mixtos, 127 solo negativos, 17 solo positivos.
- **Modelo:** `Qwen/Qwen3-4B@1cfa9a72`, bf16, en MPS.
  - Plantilla de chat sin razonamiento, la misma que en el Nivel A.
  - Activaciones fp16 en 37 capas: último token y media sobre el Lean.
- **Probe:** StandardScaler + regresión logística (C = 1).
  - Capa elegida por CV anidada en cada condición.
  - StratifiedGroupKFold(5) por enunciado, semillas 0–4.
  - Puntaje por fila: el OOF promediado entre semillas.
- **IC:** bootstrap de grupos estratificado por tipo de grupo, 2000 remuestreos, semilla 0.
- **Código:** `probe_c.py` (SHA `036568c9…`); resultados en `resultados/resultados_c_qwen3_4b.json` (SHA `1b14c216…`).
- **Segunda implementación:** `segunda_implementacion/c1_independiente.py`. La escribió un agente que no leyó `probe_c.py` ni `probes/referencia/`.

## Resultado principal (C1)

| | AUROC [IC 95 %] |
|---|---|
| Completo (NL + Lean) | 0,832 [0,807; 0,855] |
| Solo Lean | 0,678 [0,646; 0,711] |
| **Δ = completo − solo Lean** | **+0,154 [+0,121; +0,187]** |

**Decisión según la regla: positivo.**
- Por semilla: +0,144, +0,153, +0,163, +0,143, +0,155.
- La segunda implementación da +0,15354 [+0,12102; +0,18714]. Las diferencias por semilla son ≤ 3·10⁻⁴.

**Capas elegidas:**
- completo: sobre todo 31 y 36 (rango 24–36);
- solo Lean: 21–36.

## Controles (C1)

| Control | Δ (completo − control) [IC 95 %] |
|---|---|
| **Dentro de grupo** (217 grupos mixtos, mismo NL): 0,853 frente a 0,676 | **+0,177 [+0,141; +0,213]** |
| Apilado solo Lean + solo NL (0,687) | +0,146 [+0,115; +0,176] |
| Apilado, dentro de grupo | +0,176 [+0,141; +0,213] |
| NL desemparejado (0,630) | +0,202 [+0,170; +0,234] |
| NL desemparejado, dentro de grupo | +0,246 [+0,205; +0,288] |
| Solo Lean en la misma capa | +0,147 [+0,115; +0,180] |
| Superficie: n-gramas del Lean | +0,168 [+0,124; +0,213] |
| Superficie: n-gramas del Lean y del NL | +0,144 [+0,105; +0,185] |
| P(Yes) del modelo (0,788; masa 1,00) | +0,044 [+0,020; +0,069] |
| media_lean (posición secundaria) | +0,141 [+0,113; +0,171] |

**Lo que dicen estos controles:**
- Solo NL da 0,625 en global. Dentro de grupo da 0,5 por construcción, porque el NL es idéntico en todo el grupo.
- **Permutaciones** (20, control de cordura):
  - completo observado 0,809, frente a un máximo del nulo de 0,524;
  - solo Lean 0,665, frente a 0,522;
  - p = 0,048, el mínimo posible con 20 permutaciones. **Pasa.**

## Subconjuntos preespecificados (§4; se reportan, no deciden)
- **Por split:** test +0,159 [+0,105; +0,211]; valid +0,147 [+0,108; +0,188].
- **Por tipo de grupo:** mixto +0,152 [+0,119; +0,188].
- **Por libro y split** (20 subconjuntos, n = 35–403):
  - 17 de 20 tienen Δ > 0;
  - el rango va de −0,068 (valid/Shakarchi, 8 positivas) a +0,271 (test/Putnam);
  - muchos IC son anchos.
- Detalle en `resultados/subconjuntos_c1_qwen3_4b.json`.

## C2: transferencia CriticLeanBench → ProofNetVerif (secundaria)
- Se entrenó con las 450 filas que compilan de CriticLeanBench.
- La capa se eligió solo con CriticLeanBench: 36 para completo, 35 para solo Lean.

| | AUROC en ProofNetVerif |
|---|---|
| Completo | 0,761 [0,728; 0,791] |
| Solo Lean | 0,539 |
| **Δ_T** | **+0,222 [+0,176; +0,267]** |
| Δ_T dentro de grupo | +0,280 [+0,239; +0,323] |
| Completo − NL desemparejado | +0,269 [+0,233; +0,304] |

## Lectura (según la tabla del §8 de la regla, sin ir más allá)
C1 y C2 son positivos. La tabla del §8 da esta lectura: la separación más allá del Lean se replica con etiquetas humanas de otra fuente, y la dirección aprendida en CriticLeanBench transfiere entre fuentes.

En términos del probe: con un probe lineal, la etiqueta humana de ProofNetVerif **es decodificable linealmente** de las activaciones del prompt completo mejor que de las del Lean solo. Eso ocurre también **dentro del mismo enunciado** (C1-dentro), donde el NL no puede aportar dificultad ni fuente.

**Alcance:** como dice la regla, un C1 positivo indica información más allá del Lean. No prueba por sí solo que lo decodificable sea la correspondencia NL ↔ Lean. Lo más cercano a eso son:
- C1-dentro;
- NL desemparejado dentro de grupo;
- el apilado;
- el Nivel B.

## Límites
1. **Contaminación: es el límite principal.** ProofNetVerif está en Hugging Face desde el 5 feb 2025. Qwen3 se publicó el 28–29 abr 2025, sin corte de datos declarado.
   - Un C1 positivo puede reflejar memorización de pares etiquetados.
   - Kimina y DeepSeek-Prover-V2 declaran solapamiento con ProofNet.
   - Goedel-Prover-V2 hereda la exposición de Qwen3.
2. **Etiquetas:**
   - un solo anotador, con dos pasadas;
   - no se publica el acuerdo entre pasadas;
   - en la duda, el par se marca inválido;
   - los enunciados mal tipados son negativos.
3. **Negativos no compilables mezclados.** Favorecen a solo Lean, así que la prueba es conservadora.
4. **Grupos:** el n efectivo son 361 grupos, no 3752 filas.
5. **Solo un modelo.** Lineal y correlacional: separar no implica que el modelo use esa información.
6. **El probe supera a P(Yes) por poco** (+0,044). La respuesta sí/no del propio modelo ya separa bien (0,788).
7. **Formato:** el de CriticLeanBench difiere del de ProofNetVerif (`theorem dummy … := sorry`). Afecta a C2, no a C1.
8. **Comparación con `probe.py` de Carlos:** la regla del Nivel C no la exige (su §10 se cumple con la segunda implementación). Queda pendiente si Carlos la pide.

## Reproducir
```bash
zsh probes/nivel_c/lanzar.sh --probes
```
```bash
biblioteca/.venv/bin/python -I probes/nivel_c/segunda_implementacion/c1_independiente.py
```
