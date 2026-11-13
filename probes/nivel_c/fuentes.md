# Nivel C: fuentes verificadas (4 nov 2026, ~16:10 Bogotá)

Todo se consultó el 4 nov 2026 con WebFetch y con la API pública de GitHub y Hugging Face. No se llamó ninguna API de modelos. Lo que no pude abrir va marcado «[no verificado]».

## 1. DriftBench («The Faithfulness Gap», arXiv 2606.16541): existe el artículo, pero los datos NO son públicos
- Artículo: https://arxiv.org/abs/2606.16541 (Noor Islam S. Mohammad, Tamim Sheikh; v1, 15 jun 2026; CC BY 4.0, la licencia del artículo). El resumen dice que publican DriftBench, «2,183 NL/Lean 4 pairs with controlled drift labels across six subfields of mathlib4».
- Datos: **no hay descarga.** En la página del proyecto https://pmlrbd.github.io/BPF/, los botones «Code» y «DriftBench» apuntan a anclas vacías (`#`, `#driftbench`). El repositorio https://github.com/pmlrbd/BPF (Apache-2.0, árbol f811b3bf7dc092a0c0f392c337a06f1fc66d86ee) solo contiene `index.html`, `README.md` (5 bytes), `LICENSE` y un workflow de Pages. En Hugging Face, «driftbench» solo devuelve conjuntos homónimos sin relación (ideación científica, deriva de creencias). El HTML del artículo no dice dónde ni cuándo se publicará DriftBench.
- Construcción, según la página y el HTML: reglas de perturbación deterministas («not LLM sampling»), con las clases Δ∀ (cuantificador), ΔH (hipótesis omitida), ΔC (conclusión generalizada), ΔT (coerción de tipo), «combined» y «faithful». La tabla 1 da 932 pares fieles y 1 200 con deriva, que suman 2 132, no 2 183 (el artículo no explica la diferencia de 51). Hay además un split «wild» de 384 pares de un autoformalizador LLM, anotado por dos expertos (κ = 0,81); no se sabe si está incluido en los 2 183.
- **No se descargó nada.** Si se publica, sus etiquetas serían sintéticas por regla: un «drift» por construcción, no un juicio humano de adecuación. No son comparables con las de CriticLeanBench.

## 2. ShadowBench (arXiv 2608.29270): es público, pero sin pares (NL, Lean, etiqueta)
- Artículo: https://arxiv.org/abs/2608.29270 (Han et al.; v3, 5 sep 2026; EMNLP 2026; CC BY 4.0). Tiene 178 problemas de posgrado a investigación. La métrica SA-Pass da crédito completo solo si la fórmula compila, implica cada «shadow statement» y es implicada por su conjunción (chequeos de implicación en Lean). SA-Pass coincide con el juicio de expertos en el 98,8 % de los casos.
- Datos públicos:
  - https://huggingface.co/datasets/DicoTiar/ShadowBench, rev 995ce141bcaee1745149390724a053565b26d3f4, CC BY 4.0. Archivos `test.jsonl` (178) e `icml.jsonl` (126), con los campos `idx`, `informal_proof`, `formalization_rules`, `imports`.
  - https://github.com/ldilab/shadowbench, commit 362154cbb4e11d280018b50b6e7b959dbc67ae3e, **sin licencia declarada**. Tiene `data/<área>/<nivel>/<id>/{meta.json,text.md}` (179 problemas) y el código del evaluador.
- El README del repo dice textualmente: «The gold Lean formalizations and the hidden shadow checkers used for scoring are **not** included. They live only on the evaluation server». Tampoco se publican las salidas de los sistemas ni los juicios de los expertos. Es decir, **no hay ninguna formalización Lean ni ninguna etiqueta de adecuación**: solo los enunciados informales. Para usarlo habría que generar formalizaciones y enviarlas al servidor (eso es usar modelos y una API externa; está fuera de las compuertas).
- **No se descargó nada**: sin pares etiquetados no sirve para el Nivel C.
- Para el registro: las fuentes son libros de texto, apuntes, Mathlib, el Stacks project y la lista de Wiedijk, no benchmarks de competición. Los «shadows» los propone Qwen3-235B y los revisan expertos.

## 3. ProofNetVerif (tercera opción): DESCARGADO
- Artículo: Poiroux, Weiss, Kunčak, Bosselut, arXiv 2406.07222 (v3; EMNLP 2025). Datos: https://huggingface.co/datasets/PAug/ProofNetVerif, **rev 91183e5b12d64374827bf2782db629b5b0f8f319** (creado el 5 feb 2025; última modificación el 24 mar 2025), **licencia MIT** (ficha de HF; permite descargar y usar). Se descargó porque las otras dos opciones fallaron.
- Archivos, en `probes/nivel_c/datos/proofnetverif/`; SHA-256 calculado en local, igual al LFS de HF:
  - `data/valid-00000-of-00001.parquet`: d376127a467d92bcf7b42e1410b489695692d76f7af40f04d41042769751b86c (243 653 B, 2 300 filas)
  - `data/test-00000-of-00001.parquet`: 30287a8af51fc7bea2bec4fbfab6ae82ef5cf0de9f4c49b25f6ecfba4e7bb4a0 (162 896 B, 1 452 filas)
  - `README.md`: ae5d7d2c62c5329ce772d76cff49bdffec9aed375bfc881f1a6c80c53fe63e59
- Columnas: `id` (problema de ProofNet), `nl_statement`, `lean4_src_header`, `lean4_formalization` (referencia), `lean4_prediction` (formalización de un modelo), `correct`.

### Cómo se hizo la etiqueta y qué significa «adecuado»
- Es **humana**: un solo anotador, cada muestra anotada dos veces, con las predicciones anonimizadas por modelo y método y agrupadas por problema (≈ 200 horas en total con el resto del artículo). No se publica acuerdo entre anotadores.
- «Correct» = la predicción es **semánticamente equivalente** al enunciado NL (y a la referencia). Se revisan hipótesis y conclusiones (faltantes o inválidas, tipos implícitos, convenciones de ℕ, paréntesis, definiciones con otro significado), se buscan contraejemplos con plausible/slim_check, y **en caso de duda se marca inválida**. Los enunciados mal tipados se marcan inválidos.
- Negativos «naturales»: salidas reales de autoformalizadores (Llama3-8B, Llemma 7B/34B, GPT-4o, GPT-4-turbo; con pocos ejemplos, ajuste fino y muestreo). El artículo no dice qué modelo produjo cada fila [no verificado por fila].

### Comparación con CriticLeanBench
CriticLeanBench (Peng et al., ACL 2026, Sec. 3.1) usa compilador + DeepSeek-R1 + revisión humana con seis criterios.

| | CriticLeanBench | ProofNetVerif |
|---|---|---|
| Quién etiqueta | compilador → DeepSeek-R1 → humanos | un humano, dos pasadas |
| Criterio | captura el significado (6 criterios) | equivalencia semántica con el NL; la duda cuenta como inválida |
| Compilación | se sabe (50 `compile_false`) | **no se sabe** (`compila` = null); los mal tipados son negativos |
| Negativos | formalizaciones de FormalMATH/LLM que compilan y fallan | salidas reales de 5 LLM de 2024 |
| Dominio | olimpiadas y concursos | libros de pregrado (Rudin, Dummit-Foote, Munkres, Herstein, Artin…) |
| Estructura | 499 enunciados para 500 filas (casi sin pares) | 361 enunciados para 3 752 filas (1–36 por enunciado) |
| Proporción de adecuadas | 250/500 (250/450 entre las que compilan) | 1 142/3 752 (30,4 %) |

Son comparables en el concepto (adecuación semántica NL ↔ Lean juzgada por humanos), **no** en el proceso. ProofNetVerif no pasa por un juez LLM, su criterio es más estricto (la duda cuenta como inválida) y mezcla negativos que no compilan. No hay forma de quitar esos negativos sin compilar (compuerta 4).

### Formato
Todas las predicciones son `theorem dummy … := sorry`: el nombre y el cierre no cambian con la etiqueta (comprobado: 100 % en ambas clases). La cabecera (`import Mathlib`, `open …`) es la del problema. Así no hay pistas triviales de formato, pero el estilo difiere del de CriticLeanBench (`theorem <nombre> … := by sorry`), y eso importa en la transferencia.

### Riesgo de contaminación
- ProofNet (2023) y sus versiones en Lean 4 llevan años en GitHub y HF. Las **etiquetas** de ProofNetVerif son públicas en HF desde el 5 feb 2025 (y el artículo, desde jun 2024).
- Qwen3-4B se publicó el 27 abr 2025 (HF), sin corte de datos declarado. Kimina-Autoformalizer-7B es de abr 2025 [fecha no verificada hoy: la página de HF pide autenticación]. Goedel-Prover-V2-8B se publicó el 15 jul 2025 (HF).
- Los tres modelos pudieron ver los enunciados y, en principio, también los pares etiquetados. Kimina y DeepSeek-Prover-V2 tienen contaminación de ProofNet señalada en arXiv 2604.23135.
- Asimetría: CriticLeanBench (HF, 8 jul 2025) es **posterior** a Qwen3-4B y Kimina. Una caída o subida entre conjuntos puede reflejar en parte memorización. No se puede verificar; se reporta como límite.
- No hay solape de enunciados entre ProofNetVerif y CriticLeanBench: 0 grupos en común (NL normalizado).

## 4. Conversión y agrupación
Script `probes/nivel_c/preparar_proofnetverif.py`; salida en `probes/nivel_c/datos_proc/`, con resumen en `proofnetverif_resumen.json`.
- `proofnetverif.parquet` (SHA-256 2b912a38c4ba63690d60d8a1c084b828b49b8ab02db6e348cc98b7677861d695), con el esquema de `extraer.py`:
  - `id` = 0..3751 (valid y luego test);
  - `source` = `ProofNetVerif/<split>/<libro>`;
  - `refined_statement` = NL;
  - `autoformalization` = cabecera + predicción;
  - `tag` = `compile_right_is_right` (correcta) o `compile_unknown_is_false`;
  - `compila` = null;
  - columnas extra: `id_proofnet`, `split`, `lean4_formalization_ref`.
- `proofnetverif_manifiesto.jsonl` (SHA-256 1971da0913bd4b23c01fb212f34ffd8c19b9f9dc53fee571f1f39c92cfd65743): `etiqueta`, `grupo` (hash del NL normalizado, igual que `extraer.py`), `compila` (null), `grupo_tipo`, `n_grupo`.
- **Agrupación por enunciado NL normalizado**: 361 grupos, que coinciden 1:1 con el `id` de ProofNet. **217 grupos tienen ambas clases** y suman 2 695 filas; 127 solo tienen negativas y 17 solo positivas. Ningún grupo cruza valid/test. Son casi pares: dentro de un grupo el NL es fijo y solo cambia la predicción.
