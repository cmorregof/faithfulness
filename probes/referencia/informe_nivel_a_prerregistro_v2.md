# Nivel A, prerregistro v2: informe — 6 nov 2026

**Estado: PENDIENTE DE COMPARACIÓN CON `probe.py` DE CARLOS** (regla de las 12:55).
- Todo lo de abajo sale de la implementación de referencia y de `prerregistro_v2_analisis.py`.
- Nada se reporta como hallazgo hasta compararlo con `probe.py` de Carlos.

*Preliminar, sin revisión por pares.*

## Prerregistro
- **Texto:** `probes/prerregistro_v2.md`, SHA-256 `36bc53a4…`. Firmado por Carlos el 4 nov a las 22:29.
- **Confirmaciones de Carlos (5 nov):**
  - §9.7, «un modelo pasa con cualquiera de sus dos lecturas», solo con Holm sobre las 8 pruebas;
  - §9.8, un metaanálisis por lectura.

  Ambas se confirmaron después de ver la lectura (ii) y no cambian ningún umbral.
- **Datos:** CriticLeanBench, las 450 filas que compilan (250 adecuadas / 200 inadecuadas).
  - Mismas particiones, grupos y plantilla en todos los modelos.
  - Etiquetas humanas de CriticLeanBench.
- **Modelos nuevos, fijados de antemano:**
  - OLMo-2-1124-7B-Instruct;
  - Gemma-3-4B-it;
  - Llama-3.1-8B-Instruct;
  - DeepSeek-Prover-V2-7B.
- **Exploratorios:** Qwen3-4B, Goedel-Prover-V2-8B y Kimina-7B (recalculados) y Qwen3-8B (extracción incompleta).
- **Primario:** Δ = AUROC(completo) − AUROC(solo Lean), con dos lecturas:
  - (i) último token, con capa elegida por CV anidada;
  - (ii) media sobre el Lean, en una capa fija a ⌊2L/3⌋.
- **Criterio de réplica por modelo:** una lectura pasa si cumple las dos cosas:
  - p de 1000 permutaciones, con Holm sobre 8 pruebas, < 0,05;
  - IC de completo − apilado entero por encima de 0.
- **Afirmación global:** ≥ 3 de 4 modelos pasan **y** el IC del metaanálisis de efectos aleatorios (DerSimonian–Laird) queda entero por encima de 0, en la misma lectura.

## Resultados

### Modelos nuevos

**Lectura (i), último token:**

| Modelo | Completo | Solo Lean | Δ [IC 95 %] | Completo − apilado [IC] | p (1000 perm.) |
|---|---|---|---|---|---|
| OLMo-2-7B | 0,738 | 0,705 | +0,032 [−0,011; +0,075] | +0,032 [−0,007; +0,069] | 0,195 |
| Gemma-3-4B | 0,726 | 0,688 | +0,038 [−0,009; +0,085] | +0,013 [−0,029; +0,055] | no se corre (decisión de Carlos, 6 nov 14:34) |
| Llama-3.1-8B | 0,712 | 0,723 | −0,011 [−0,056; +0,031] | −0,059 [−0,098; −0,021] | no se corre (decisión de Carlos, 6 nov 14:34) |
| DeepSeek-Prover-V2 | 0,684 | 0,627 | +0,056 [+0,008; +0,104] | +0,043 [+0,003; +0,085] | 0,084 |

**Lectura (ii), media sobre el Lean, capa fija:**

| Modelo | Completo | Solo Lean | Δ [IC 95 %] | Completo − apilado [IC] | p (1000 perm.) |
|---|---|---|---|---|---|
| OLMo-2-7B | 0,724 | 0,679 | +0,044 [+0,009; +0,079] | +0,049 [+0,014; +0,083] | 0,084 |
| Gemma-3-4B | 0,745 | 0,688 | +0,058 [+0,021; +0,094] | +0,067 [+0,030; +0,102] | 0,040 |
| Llama-3.1-8B | 0,736 | 0,682 | +0,054 [+0,018; +0,088] | +0,056 [+0,021; +0,089] | 0,040 |
| DeepSeek-Prover-V2 | 0,704 | 0,678 | +0,025 [−0,008; +0,061] | +0,033 [−0,001; +0,067] | 0,19 |

P(Yes) de DeepSeek-Prover-V2 no es interpretable: la masa de P(Yes) + P(No) es ≈ 0.

### Metaanálisis (DerSimonian–Laird; EE = DE bootstrap de Δ; IC normal)

| Conjunto | Lectura | Estimación [IC 95 %] | τ² | I² |
|---|---|---|---|---|
| 4 modelos nuevos (prerregistrado) | (ii) | **+0,045 [+0,028; +0,063]** | 0 | 0 % |
| 4 modelos nuevos (prerregistrado) | (i) | +0,028 [−0,000; +0,056] | 0,00028 | 34 % |
| 7 modelos (exploratorio) | (ii) | +0,056 [+0,041; +0,071] | 0,00010 | 25 % |
| 7 modelos (exploratorio) | (i) | +0,041 [+0,020; +0,063] | 0,00033 | 40 % |

### Controles

| Control | Completo | Solo Lean | Δ |
|---|---|---|---|
| Qwen3-4B con pesos aleatorios, lectura (i) | — | — | +0,008 [−0,041; +0,056] |
| Qwen3-4B con pesos aleatorios, lectura (ii) | — | — | −0,073 [−0,133; −0,011]; p = 0,93 |
| Embeddings `BAAI/bge-m3` | 0,544 | 0,642 | −0,098 [−0,153; −0,044] |

### Exploratorios recalculados

| Modelo | Etiqueta | Δ (i) | Δ (ii) | p (ii) |
|---|---|---|---|---|
| Qwen3-4B | exploratorio | +0,091 | +0,095 | 0,002 |
| Goedel-V2-8B | réplica fallida, recalculado | +0,043 | +0,066 | 0,002 |
| Kimina-7B | réplica fallida, recalculado | +0,044 | +0,051 | 0,062 |

## Decisión según el prerregistro v2
**Ninguno de los 4 modelos nuevos pasa, y la afirmación global no se cumple.**
- **Lectura (ii):** ningún p alcanza el umbral de Holm para 8 pruebas. El p más pequeño tendría que ser < 0,00625, y el mínimo observado es 0,040.
- **Lectura (i):**
  - el IC de completo − apilado solo excluye 0 en DeepSeek, y su p es 0,084;
  - OLMo, Gemma y Llama no cumplen la condición del apilado, así que las permutaciones que faltan no pueden cambiar esta conclusión.

**Frase honesta:** con 450 filas por modelo, el instrumento no resuelve el efecto modelo por modelo. Agrupados, los cuatro modelos nuevos dan en la lectura (ii) un Δ pequeño:
- del mismo signo en los cuatro;
- homogéneo (I² = 0 %);
- con un metaanálisis de +0,045 [+0,028; +0,063].

Los dos controles nulos (pesos aleatorios y embeddings) no van en esa dirección. Por la regla, eso **no basta** para afirmar la réplica.

## Desviaciones anotadas en la bitácora
1. **`extraer.py`:** usa la máscara por prefijo cuando los offsets del tokenizador no cuadran. Solo cambia DeepSeek (1972 de 2000 prompts).
2. **`prerregistro_v2_analisis.py`, error en la matriz de permutaciones de la lectura (i):** se corrigió el 5 nov a las 08:37 y se relanzó DeepSeek. No afecta a la lectura (ii).
3. **Qwen3-8B (exploratorio):** quedó en 300 de 500 filas porque no cabe en memoria junto a otros procesos.
4. **Llama:** se reanudó desde lo guardado después de atascarse por memoria.
5. **Mac:** se reinició el 5 nov hacia las 21:51 y se perdieron las permutaciones (i) de Gemma. Se relanzaron en la cola de la sesión de la noche.

## Pendiente
- **Comparar con `probe.py` de Carlos.** Es la condición para reportar.
- **Permutaciones (i):** solo completan la tabla. OLMo terminó el 6 nov a las 16:11 (p = 0,195); las de Gemma y Llama no se corren (decisión de Carlos del 6 nov a las 14:34), porque no pueden cambiar la decisión: su IC de completo − apilado en la lectura (i) ya incluye 0.
