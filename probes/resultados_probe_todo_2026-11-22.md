# `probe.py` frente a la referencia: Nivel A en ocho modelos y Nivel C en dos (corrida del 22 nov 2026)

Encargo: `probes/ENCARGO_probe_todo_2026-11-22.md`. La corrida se hizo en el Mac de Carlos, entre las 22:08 del 22 nov y las 00:04 del 23 nov, hora de Bogotá. `probe.py` no se modificó: SHA-256 `bbdb16350b88494e7c1c6a0d5c51b3003ea41d690327378fb58f06dc697dc30f`.

## Resultado

Las cifras coinciden y una decisión no. `probe.py` se comparó con la referencia en 18 lecturas: las dos lecturas del Nivel A en ocho modelos y la prueba central del Nivel C en dos. En las 18, AUROC(completo), AUROC(solo_lean) y Δ quedan dentro de 0.005 de la referencia. La mayor diferencia es 0.0033.

La decisión, que es el lado del cero en que cae el intervalo del 95 % de Δ, es la misma en 17 de las 18. La excepción es Qwen3-8B en la lectura (i) del Nivel A. Ahí `probe.py` da Δ = +0.0457 [+0.0016, +0.0914] y la referencia +0.0429 [−0.0041, +0.0882]. La diferencia puntual es +0.0027, dentro de la tolerancia, pero el intervalo de `probe.py` queda por encima de cero y el de la referencia lo incluye. Con la regla escrita en la bitácora antes de correr, eso cuenta como un cambio de decisión.

Por esa excepción no se tocó el artículo ni el README, como manda el paso 5 del encargo. Al final de este informe queda la frase propuesta para que Carlos decida.

Los cuatro modelos prerregistrados del Nivel A coinciden en las dos lecturas, en cifras y en decisión. Qwen3-8B es un modelo exploratorio en el artículo, que ya reporta para él un intervalo que incluye el cero en la lectura (i).

El Nivel B no se comparó, porque su cifra principal es una AUROC pareada que `probe.py` no calcula.

## Qué se comparó y qué no

Se comparó el contraste central, Δ = AUROC(completo) − AUROC(solo_lean), con sus dos AUROC y el intervalo de Δ.

- **Nivel A.** 450 filas que compilan (250 y 200). Lectura (i): `ultimo`, capa por validación anidada. Lectura (ii): `media_lean`, capa fija ⌊2L/3⌋. Ocho modelos: Qwen3-4B, los cuatro prerregistrados (OLMo-2-7B, Gemma-3-4B, Llama-3.1-8B, DeepSeek-Prover-V2-7B) y tres exploratorios (Goedel-Prover-V2-8B, Kimina-7B y Qwen3-8B).
- **Nivel C.** Prueba central C1 de `nivel_c/regla_borrador.md`: las 3752 filas de ProofNetVerif, `ultimo`, capa por validación anidada, bootstrap de enunciados estratificado por tipo de grupo. Dos modelos: Qwen3-4B, que es el de la regla aprobada, y Llama-3.1-8B, exploratorio.

`probe.py` no hace permutaciones ni control apilado. Por eso esta comparación no reproduce el veredicto de «pasa o no pasa» del prerregistro v2, ni la corrección de Holm, ni el metaanálisis. La lista completa de lo que quedó sin comparar está más abajo.

## Nivel A

| Modelo | Lectura | Cantidad | `probe.py` | Referencia | Diferencia | ¿Dentro de 0.005? | ¿Misma decisión? |
|---|---|---|---|---|---|---|---|
| Qwen3-4B | (i) | AUROC(completo) | 0.8114 [0.7710, 0.8493] | 0.8143 [0.7716, 0.8524] | −0.0029 | sí |  |
| Qwen3-4B | (i) | AUROC(solo_lean) | 0.7231 [0.6766, 0.7669] | 0.7230 [0.6764, 0.7683] | +0.0001 | sí |  |
| Qwen3-4B | (i) | Δ | +0.0883 [+0.0415, +0.1351] | +0.0913 [+0.0428, +0.1366] | −0.0030 | sí | sí (por encima / por encima) |
| Qwen3-4B | (ii) | AUROC(completo) | 0.7512 [0.7054, 0.7948] | 0.7510 [0.7046, 0.7964] | +0.0002 | sí |  |
| Qwen3-4B | (ii) | AUROC(solo_lean) | 0.6552 [0.6048, 0.7040] | 0.6558 [0.6048, 0.7037] | −0.0006 | sí |  |
| Qwen3-4B | (ii) | Δ | +0.0960 [+0.0550, +0.1348] | +0.0952 [+0.0571, +0.1343] | +0.0008 | sí | sí (por encima / por encima) |
| OLMo-2-7B | (i) | AUROC(completo) | 0.7361 [0.6904, 0.7793] | 0.7376 [0.6934, 0.7806] | −0.0015 | sí |  |
| OLMo-2-7B | (i) | AUROC(solo_lean) | 0.7054 [0.6564, 0.7557] | 0.7052 [0.6566, 0.7546] | +0.0002 | sí |  |
| OLMo-2-7B | (i) | Δ | +0.0307 [−0.0141, +0.0746] | +0.0324 [−0.0115, +0.0750] | −0.0017 | sí | sí (incluye 0 / incluye 0) |
| OLMo-2-7B | (ii) | AUROC(completo) | 0.7231 [0.6754, 0.7667] | 0.7239 [0.6774, 0.7706] | −0.0008 | sí |  |
| OLMo-2-7B | (ii) | AUROC(solo_lean) | 0.6792 [0.6255, 0.7263] | 0.6795 [0.6303, 0.7279] | −0.0003 | sí |  |
| OLMo-2-7B | (ii) | Δ | +0.0439 [+0.0106, +0.0775] | +0.0444 [+0.0086, +0.0789] | −0.0005 | sí | sí (por encima / por encima) |
| Gemma-3-4B | (i) | AUROC(completo) | 0.7254 [0.6803, 0.7703] | 0.7257 [0.6789, 0.7711] | −0.0004 | sí |  |
| Gemma-3-4B | (i) | AUROC(solo_lean) | 0.6879 [0.6370, 0.7366] | 0.6881 [0.6382, 0.7354] | −0.0002 | sí |  |
| Gemma-3-4B | (i) | Δ | +0.0374 [−0.0116, +0.0846] | +0.0376 [−0.0089, +0.0847] | −0.0002 | sí | sí (incluye 0 / incluye 0) |
| Gemma-3-4B | (ii) | AUROC(completo) | 0.7449 [0.7002, 0.7873] | 0.7453 [0.7000, 0.7914] | −0.0004 | sí |  |
| Gemma-3-4B | (ii) | AUROC(solo_lean) | 0.6872 [0.6360, 0.7336] | 0.6878 [0.6360, 0.7370] | −0.0006 | sí |  |
| Gemma-3-4B | (ii) | Δ | +0.0577 [+0.0215, +0.0936] | +0.0576 [+0.0214, +0.0936] | +0.0001 | sí | sí (por encima / por encima) |
| Llama-3.1-8B | (i) | AUROC(completo) | 0.7115 [0.6641, 0.7573] | 0.7117 [0.6637, 0.7571] | −0.0002 | sí |  |
| Llama-3.1-8B | (i) | AUROC(solo_lean) | 0.7238 [0.6775, 0.7710] | 0.7228 [0.6759, 0.7688] | +0.0009 | sí |  |
| Llama-3.1-8B | (i) | Δ | −0.0123 [−0.0563, +0.0297] | −0.0112 [−0.0564, +0.0313] | −0.0011 | sí | sí (incluye 0 / incluye 0) |
| Llama-3.1-8B | (ii) | AUROC(completo) | 0.7348 [0.6909, 0.7784] | 0.7356 [0.6878, 0.7796] | −0.0008 | sí |  |
| Llama-3.1-8B | (ii) | AUROC(solo_lean) | 0.6824 [0.6304, 0.7298] | 0.6820 [0.6341, 0.7289] | +0.0003 | sí |  |
| Llama-3.1-8B | (ii) | Δ | +0.0524 [+0.0176, +0.0894] | +0.0536 [+0.0184, +0.0883] | −0.0012 | sí | sí (por encima / por encima) |
| DeepSeek-Prover-V2-7B | (i) | AUROC(completo) | 0.6847 [0.6371, 0.7359] | 0.6839 [0.6367, 0.7312] | +0.0009 | sí |  |
| DeepSeek-Prover-V2-7B | (i) | AUROC(solo_lean) | 0.6261 [0.5723, 0.6782] | 0.6274 [0.5787, 0.6768] | −0.0013 | sí |  |
| DeepSeek-Prover-V2-7B | (i) | Δ | +0.0586 [+0.0083, +0.1063] | +0.0564 [+0.0084, +0.1042] | +0.0022 | sí | sí (por encima / por encima) |
| DeepSeek-Prover-V2-7B | (ii) | AUROC(completo) | 0.7039 [0.6547, 0.7509] | 0.7037 [0.6554, 0.7534] | +0.0002 | sí |  |
| DeepSeek-Prover-V2-7B | (ii) | AUROC(solo_lean) | 0.6779 [0.6289, 0.7248] | 0.6783 [0.6274, 0.7271] | −0.0004 | sí |  |
| DeepSeek-Prover-V2-7B | (ii) | Δ | +0.0260 [−0.0092, +0.0609] | +0.0254 [−0.0082, +0.0612] | +0.0006 | sí | sí (incluye 0 / incluye 0) |
| Goedel-Prover-V2-8B | (i) | AUROC(completo) | 0.8023 [0.7608, 0.8397] | 0.8006 [0.7577, 0.8415] | +0.0017 | sí |  |
| Goedel-Prover-V2-8B | (i) | AUROC(solo_lean) | 0.7578 [0.7122, 0.8000] | 0.7572 [0.7137, 0.8002] | +0.0006 | sí |  |
| Goedel-Prover-V2-8B | (i) | Δ | +0.0445 [+0.0055, +0.0851] | +0.0434 [+0.0048, +0.0820] | +0.0011 | sí | sí (por encima / por encima) |
| Goedel-Prover-V2-8B | (ii) | AUROC(completo) | 0.7489 [0.7027, 0.7941] | 0.7490 [0.7012, 0.7931] | −0.0001 | sí |  |
| Goedel-Prover-V2-8B | (ii) | AUROC(solo_lean) | 0.6839 [0.6322, 0.7324] | 0.6828 [0.6329, 0.7309] | +0.0011 | sí |  |
| Goedel-Prover-V2-8B | (ii) | Δ | +0.0650 [+0.0365, +0.0956] | +0.0662 [+0.0373, +0.0936] | −0.0013 | sí | sí (por encima / por encima) |
| Kimina-7B | (i) | AUROC(completo) | 0.7474 [0.7032, 0.7901] | 0.7492 [0.7038, 0.7929] | −0.0017 | sí |  |
| Kimina-7B | (i) | AUROC(solo_lean) | 0.7053 [0.6532, 0.7537] | 0.7055 [0.6578, 0.7511] | −0.0002 | sí |  |
| Kimina-7B | (i) | Δ | +0.0421 [+0.0013, +0.0823] | +0.0437 [+0.0048, +0.0836] | −0.0016 | sí | sí (por encima / por encima) |
| Kimina-7B | (ii) | AUROC(completo) | 0.7496 [0.7031, 0.7956] | 0.7505 [0.7044, 0.7952] | −0.0010 | sí |  |
| Kimina-7B | (ii) | AUROC(solo_lean) | 0.7004 [0.6496, 0.7489] | 0.6999 [0.6499, 0.7472] | +0.0004 | sí |  |
| Kimina-7B | (ii) | Δ | +0.0492 [+0.0122, +0.0874] | +0.0506 [+0.0146, +0.0875] | −0.0014 | sí | sí (por encima / por encima) |
| Qwen3-8B | (i) | AUROC(completo) | 0.7502 [0.7061, 0.7934] | 0.7469 [0.6992, 0.7916] | +0.0033 | sí |  |
| Qwen3-8B | (i) | AUROC(solo_lean) | 0.7045 [0.6557, 0.7503] | 0.7040 [0.6535, 0.7526] | +0.0006 | sí |  |
| Qwen3-8B | (i) | Δ | +0.0457 [+0.0016, +0.0914] | +0.0429 [−0.0041, +0.0882] | +0.0027 | sí | NO (por encima / incluye 0) |
| Qwen3-8B | (ii) | AUROC(completo) | 0.7766 [0.7355, 0.8155] | 0.7753 [0.7308, 0.8182] | +0.0013 | sí |  |
| Qwen3-8B | (ii) | AUROC(solo_lean) | 0.6906 [0.6414, 0.7366] | 0.6894 [0.6412, 0.7371] | +0.0012 | sí |  |
| Qwen3-8B | (ii) | Δ | +0.0859 [+0.0515, +0.1213] | +0.0858 [+0.0516, +0.1189] | +0.0001 | sí | sí (por encima / por encima) |

En la columna de decisión, el primer rótulo es el de `probe.py` y el segundo el de la referencia. Los intervalos de las AUROC se dan para completar la tabla; la regla solo fija tolerancia sobre los valores puntuales y decisión sobre el intervalo de Δ.

### La lectura que cambia de decisión: Qwen3-8B, lectura (i)

El intervalo de Δ cruza el cero en la referencia por 0.004 y lo esquiva en `probe.py` por 0.002. Los dos límites inferiores están a menos de 0.005 de cero, que es la tolerancia de la regla, así que un desplazamiento de 0.003 en el valor puntual basta para cambiar de lado. Desde fuera, sin leer el código de la referencia, veo esto:

1. *La diferencia está en los puntajes de completo.* AUROC(completo) difiere en +0.0033 y AUROC(solo_lean) en +0.0006. En completo las dos implementaciones eligen la misma capa en 24 de las 25 particiones externas. En la que falta (semilla 0, partición 4), `probe.py` elige la capa 29 y la referencia la 22. En solo_lean coinciden las 25.
2. *El bootstrap no la explica.* Apliqué `diferencia_pareada` de `probe.py`, sin cambios, a los puntajes que la referencia guardó en su `.npz`. Da +0.0429 [−0.0010, +0.0876], que también incluye el cero. Con los mismos puntajes las dos maneras de remuestrear llegan a la misma decisión, así que el cambio viene de los puntajes (`salida/nivel_a/diagnostico_ic.json`).
3. *El solver es una causa compatible.* La bitácora (4 nov, 23:34) y `referencia/v2_validacion_solver_qwen3_4b.json` dicen que la referencia del Nivel A usa un «solver v2» propio, validado contra sklearn dentro de ±0.005 en Qwen3-4B, con la capa igual en 24 de 25 particiones. `probe.py` usa sklearn. Dos solvers que convergen a puntos algo distintos pueden ordenar distinto dos capas casi empatadas en la validación interna, y eso es lo que se ve aquí. No comprobé esta causa, porque hacerlo exige leer o ejecutar el código de la referencia.

Otras lecturas tienen el límite inferior del intervalo igual de cerca de cero y conservan la decisión. Por ejemplo, en Kimina (i) el límite de `probe.py` es +0.0013 frente a +0.0048 de la referencia, en Goedel (i) es +0.0055 frente a +0.0048 y en DeepSeek-Prover-V2 (i) es +0.0083 frente a +0.0084.

No ajusté ningún parámetro ni repetí nada con otra semilla.

### Capas de la lectura (i) frente a la referencia

| Modelo | Capas iguales, completo | Capas iguales, solo_lean | Particiones con capa distinta (semilla, partición: `probe.py` / referencia) |
|---|---|---|---|
| Qwen3-4B | 24 de 25 | 25 de 25 | completo s2 p3: 23 / 36 |
| OLMo-2-7B | 23 de 25 | 25 de 25 | completo s1 p1: 23 / 24; completo s2 p5: 28 / 30 |
| Gemma-3-4B | 25 de 25 | 21 de 25 | solo_lean s0 p3: 32 / 2; solo_lean s0 p4: 16 / 17; solo_lean s1 p2: 27 / 26; solo_lean s4 p3: 17 / 18 |
| Llama-3.1-8B | 25 de 25 | 24 de 25 | solo_lean s1 p5: 31 / 32 |
| DeepSeek-Prover-V2-7B | 25 de 25 | 24 de 25 | solo_lean s3 p4: 29 / 30 |
| Goedel-Prover-V2-8B | 21 de 25 | 25 de 25 | completo s0 p1: 28 / 29; completo s0 p4: 24 / 28; completo s2 p3: 26 / 25; completo s4 p1: 29 / 28 |
| Kimina-7B | 24 de 25 | 25 de 25 | completo s1 p5: 19 / 18 |
| Qwen3-8B | 24 de 25 | 25 de 25 | completo s0 p4: 29 / 22 |

De las 400 selecciones de capa (ocho modelos, dos condiciones, 25 particiones), 385 coinciden. Las 15 que difieren están repartidas entre los ocho modelos, y en diez de ellas las dos capas son vecinas.

### Capas elegidas por `probe.py` en la lectura (i)

Cada celda es una semilla, con sus cinco particiones externas.

| Modelo | Condición | Semilla 0 | Semilla 1 | Semilla 2 | Semilla 3 | Semilla 4 |
|---|---|---|---|---|---|---|
| Qwen3-4B | completo | 36, 36, 26, 36, 36 | 36, 36, 36, 36, 36 | 36, 36, 23, 36, 36 | 36, 36, 36, 36, 36 | 36, 36, 36, 36, 36 |
| Qwen3-4B | solo_lean | 36, 23, 35, 3, 36 | 23, 36, 29, 35, 23 | 3, 23, 36, 22, 23 | 22, 23, 16, 36, 35 | 35, 2, 23, 35, 36 |
| OLMo-2-7B | completo | 14, 29, 30, 31, 28 | 23, 30, 28, 23, 32 | 11, 23, 14, 29, 28 | 32, 26, 29, 30, 26 | 7, 28, 30, 24, 29 |
| OLMo-2-7B | solo_lean | 31, 5, 7, 23, 16 | 13, 29, 5, 16, 7 | 8, 16, 30, 16, 14 | 31, 5, 7, 5, 5 | 5, 31, 22, 7, 5 |
| Gemma-3-4B | completo | 10, 5, 31, 31, 22 | 22, 15, 32, 34, 33 | 9, 31, 22, 34, 31 | 22, 34, 34, 16, 22 | 22, 22, 6, 22, 31 |
| Gemma-3-4B | solo_lean | 18, 2, 32, 16, 31 | 17, 27, 21, 31, 2 | 17, 2, 2, 2, 2 | 17, 2, 21, 17, 10 | 7, 23, 17, 4, 2 |
| Llama-3.1-8B | completo | 18, 12, 9, 21, 21 | 18, 15, 5, 8, 21 | 5, 5, 22, 15, 30 | 22, 21, 13, 9, 4 | 12, 16, 13, 24, 19 |
| Llama-3.1-8B | solo_lean | 12, 27, 6, 17, 28 | 27, 32, 8, 12, 31 | 32, 30, 12, 28, 32 | 32, 30, 9, 32, 8 | 27, 32, 30, 32, 6 |
| DeepSeek-Prover-V2-7B | completo | 6, 7, 30, 16, 18 | 4, 18, 4, 18, 29 | 18, 8, 8, 17, 7 | 18, 16, 5, 17, 30 | 30, 16, 19, 18, 30 |
| DeepSeek-Prover-V2-7B | solo_lean | 2, 7, 12, 4, 5 | 11, 2, 7, 10, 4 | 2, 4, 8, 30, 8 | 29, 24, 4, 29, 10 | 2, 4, 1, 6, 6 |
| Goedel-Prover-V2-8B | completo | 28, 29, 30, 24, 27 | 28, 28, 29, 36, 30 | 34, 28, 26, 33, 35 | 30, 24, 34, 27, 28 | 29, 28, 22, 28, 34 |
| Goedel-Prover-V2-8B | solo_lean | 23, 23, 23, 23, 23 | 22, 23, 23, 23, 23 | 23, 23, 23, 23, 23 | 22, 23, 22, 23, 23 | 23, 23, 23, 23, 22 |
| Kimina-7B | completo | 23, 19, 27, 19, 26 | 25, 25, 9, 25, 19 | 18, 25, 22, 25, 22 | 25, 11, 27, 19, 26 | 27, 9, 19, 19, 19 |
| Kimina-7B | solo_lean | 22, 22, 12, 25, 23 | 25, 14, 24, 23, 16 | 5, 26, 16, 18, 24 | 22, 13, 28, 23, 23 | 23, 28, 13, 23, 24 |
| Qwen3-8B | completo | 34, 34, 33, 29, 23 | 34, 32, 24, 34, 36 | 23, 34, 29, 29, 36 | 34, 23, 29, 29, 29 | 21, 29, 28, 29, 36 |
| Qwen3-8B | solo_lean | 21, 31, 20, 20, 21 | 1, 21, 21, 34, 20 | 21, 17, 21, 21, 21 | 21, 21, 21, 21, 18 | 20, 21, 31, 25, 35 |

### Correlación fila a fila de los puntajes (450 filas)

| Modelo | Lectura | Condición | Pearson | Spearman | Mayor diferencia absoluta | `y` idéntico |
|---|---|---|---|---|---|---|
| Qwen3-4B | (i) | completo | 0.9979 | 0.9976 | 0.177 | sí |
| Qwen3-4B | (i) | solo_lean | 0.9999 | 0.9999 | 0.020 | sí |
| Qwen3-4B | (ii) | completo | 0.9998 | 0.9999 | 0.052 | sí |
| Qwen3-4B | (ii) | solo_lean | 0.9999 | 0.9999 | 0.053 | sí |
| OLMo-2-7B | (i) | completo | 0.9989 | 0.9990 | 0.183 | sí |
| OLMo-2-7B | (i) | solo_lean | 0.9999 | 0.9999 | 0.022 | sí |
| OLMo-2-7B | (ii) | completo | 0.9997 | 0.9997 | 0.068 | sí |
| OLMo-2-7B | (ii) | solo_lean | 0.9998 | 0.9998 | 0.052 | sí |
| Gemma-3-4B | (i) | completo | 0.9999 | 0.9999 | 0.024 | sí |
| Gemma-3-4B | (i) | solo_lean | 0.9890 | 0.9892 | 0.204 | sí |
| Gemma-3-4B | (ii) | completo | 0.9999 | 0.9998 | 0.047 | sí |
| Gemma-3-4B | (ii) | solo_lean | 0.9999 | 0.9998 | 0.047 | sí |
| Llama-3.1-8B | (i) | completo | 0.9999 | 0.9999 | 0.034 | sí |
| Llama-3.1-8B | (i) | solo_lean | 0.9992 | 0.9991 | 0.114 | sí |
| Llama-3.1-8B | (ii) | completo | 0.9998 | 0.9998 | 0.054 | sí |
| Llama-3.1-8B | (ii) | solo_lean | 0.9998 | 0.9999 | 0.037 | sí |
| DeepSeek-Prover-V2-7B | (i) | completo | 0.9999 | 0.9999 | 0.029 | sí |
| DeepSeek-Prover-V2-7B | (i) | solo_lean | 0.9996 | 0.9996 | 0.058 | sí |
| DeepSeek-Prover-V2-7B | (ii) | completo | 0.9997 | 0.9997 | 0.053 | sí |
| DeepSeek-Prover-V2-7B | (ii) | solo_lean | 0.9997 | 0.9997 | 0.062 | sí |
| Goedel-Prover-V2-8B | (i) | completo | 0.9983 | 0.9984 | 0.206 | sí |
| Goedel-Prover-V2-8B | (i) | solo_lean | 0.9999 | 0.9999 | 0.029 | sí |
| Goedel-Prover-V2-8B | (ii) | completo | 0.9997 | 0.9997 | 0.081 | sí |
| Goedel-Prover-V2-8B | (ii) | solo_lean | 0.9998 | 0.9997 | 0.046 | sí |
| Kimina-7B | (i) | completo | 0.9986 | 0.9965 | 0.163 | sí |
| Kimina-7B | (i) | solo_lean | 0.9999 | 0.9999 | 0.032 | sí |
| Kimina-7B | (ii) | completo | 0.9997 | 0.9997 | 0.079 | sí |
| Kimina-7B | (ii) | solo_lean | 0.9997 | 0.9997 | 0.077 | sí |
| Qwen3-8B | (i) | completo | 0.9968 | 0.9974 | 0.189 | sí |
| Qwen3-8B | (i) | solo_lean | 0.9999 | 0.9999 | 0.031 | sí |
| Qwen3-8B | (ii) | completo | 0.9996 | 0.9996 | 0.079 | sí |
| Qwen3-8B | (ii) | solo_lean | 0.9998 | 0.9998 | 0.046 | sí |

El vector `y` de `probe.py` y el de los `.npz` de la referencia son idénticos en los ocho modelos, así que el orden de las filas es el mismo. Las correlaciones más bajas, entre 0.989 y 0.999, aparecen en la lectura (i) y en la condición donde alguna partición eligió otra capa. En la lectura (ii), que no elige capa, ninguna baja de 0.9996.

### Barajadas (detector de fugas)

`control_barajadas` una vez por modelo, en `ultimo`, en las capas ⌊L/3⌋, ⌊2L/3⌋ y L, con cinco barajes.

| Modelo | Capas | Media de la AUROC barajada por capa | Rango de los quince valores |
|---|---|---|---|
| Qwen3-4B | 12, 24, 36 | 0.490, 0.473, 0.472 | 0.411 a 0.549 |
| OLMo-2-7B | 10, 21, 32 | 0.487, 0.508, 0.492 | 0.433 a 0.563 |
| Gemma-3-4B | 11, 22, 34 | 0.477, 0.459, 0.479 | 0.406 a 0.549 |
| Llama-3.1-8B | 10, 21, 32 | 0.492, 0.515, 0.510 | 0.449 a 0.556 |
| DeepSeek-Prover-V2-7B | 10, 20, 30 | 0.485, 0.494, 0.474 | 0.434 a 0.532 |
| Goedel-Prover-V2-8B | 12, 24, 36 | 0.481, 0.471, 0.481 | 0.394 a 0.542 |
| Kimina-7B | 9, 18, 28 | 0.492, 0.505, 0.500 | 0.430 a 0.554 |
| Qwen3-8B | 12, 24, 36 | 0.480, 0.455, 0.467 | 0.398 a 0.545 |

Las medias rondan 0.5, entre 0.455 y 0.515, sin señal de fuga.

### Qwen3-4B en el Mac frente a la corrida Linux del 21 nov

Los puntajes no coinciden bit a bit, pero las conclusiones son las mismas. Las 50 capas elegidas son iguales. Los resúmenes (AUROC, Δ e intervalos) difieren como mucho en 0.0005 y las barajadas en 0.0005. En los puntajes por fila la diferencia máxima es 0.0098 en la lectura (i) y 0.0053 en la (ii), con medianas por debajo de 0.0005. La causa probable es el BLAS: Accelerate en el Mac y OpenBLAS en la máquina Linux, con los mismos numpy 2.5.4 y scikit-learn 1.9.1.

| Lectura | Cantidad | Mac (22 nov) | Linux (21 nov) |
|---|---|---|---|
| (i) | AUROC(completo) | 0.8114 [0.7710, 0.8493] | 0.8114 [0.7712, 0.8493] |
| (i) | AUROC(solo_lean) | 0.7231 [0.6766, 0.7669] | 0.7230 [0.6765, 0.7669] |
| (i) | Δ | +0.0883 [+0.0415, +0.1351] | +0.0884 [+0.0417, +0.1356] |
| (ii) | AUROC(completo) | 0.7512 [0.7054, 0.7948] | 0.7512 [0.7052, 0.7949] |
| (ii) | AUROC(solo_lean) | 0.6552 [0.6048, 0.7040] | 0.6552 [0.6047, 0.7040] |
| (ii) | Δ | +0.0960 [+0.0550, +0.1348] | +0.0960 [+0.0552, +0.1349] |

El artículo cita hoy las cifras de la corrida Linux (+0.088 [0.042, 0.136] y +0.096 [0.055, 0.135]). Con la corrida del Mac los dos límites de la lectura (i) redondean a 0.041 y 0.135.

### `main` entero de Qwen3-4B

`probe.main` corrió una vez, entero, en 3239 s (54 minutos, un hilo, con otros cinco procesos en la máquina). Su informe y sus cuatro figuras están en `corrida_probe_todo_2026-11-22/main_qwen3_4b/`. Se llamó con `parquet_en_orden=True`, porque el parquet no trae columna `idx`, y con la ruta de salida en esa carpeta.

En las 450 filas `main` da las mismas cifras que la corrida por piezas: lectura (i) 0.811, 0.723 y Δ = +0.088 [0.041, 0.135], con las mismas 50 capas; lectura (ii) 0.751, 0.655 y Δ = +0.096 [0.055, 0.135]. Eso confirma que llamar a las funciones por separado no cambia nada.

`main` calcula además tres cosas que la regla de esta comparación no cubre. Las anoto porque la referencia guarda dos de ellas como secundarias en `v2_resultados_qwen3_4b.json`:

| Medida, 450 filas | `probe.py` | Referencia |
|---|---|---|
| P(Yes) completo | 0.699 [0.653, 0.745] | 0.699 |
| Superficie del Lean | 0.670 [0.621, 0.719] | 0.682 |
| Barajadas, máximo entre las 37 capas | 0.506 en `ultimo`, 0.525 en `media_lean` | |

P(Yes) coincide. La superficie difiere en 0.012. Las dos líneas de base no están definidas igual: `linea_base_superficie` de `probe.py` usa conteos de unigramas y bigramas más el logaritmo de la longitud, y el apéndice del artículo describe el control de la referencia con n-gramas binarios. Esta cifra no entra en la tolerancia, pero conviene que Carlos sepa que ahí las dos implementaciones no miden lo mismo.

En las 500 filas, que incluyen las 50 que no compilan, `main` da Δ = +0.112 [0.069, 0.155] en la lectura (i) y +0.127 [0.091, 0.163] en la (ii). La referencia v2 no tiene ese análisis, así que no hay con qué compararlo.

## Nivel C

| Modelo | Lectura | Cantidad | `probe.py` | Referencia | Diferencia | ¿Dentro de 0.005? | ¿Misma decisión? |
|---|---|---|---|---|---|---|---|
| Qwen3-4B | `ultimo`, capa anidada | AUROC(completo) | 0.8320 [0.8074, 0.8546] | 0.8320 [0.8073, 0.8552] | +0.0000 | sí |  |
| Qwen3-4B | `ultimo`, capa anidada | AUROC(solo_lean) | 0.6785 [0.6463, 0.7112] | 0.6785 [0.6459, 0.7112] | +0.0000 | sí |  |
| Qwen3-4B | `ultimo`, capa anidada | Δ | +0.1536 [+0.1198, +0.1867] | +0.1536 [+0.1211, +0.1871] | +0.0000 | sí | sí (por encima / por encima) |
| Llama-3.1-8B | `ultimo`, capa anidada | AUROC(completo) | 0.7913 [0.7647, 0.8181] | 0.7913 [0.7657, 0.8191] | +0.0000 | sí |  |
| Llama-3.1-8B | `ultimo`, capa anidada | AUROC(solo_lean) | 0.6640 [0.6269, 0.7013] | 0.6640 [0.6260, 0.7028] | +0.0000 | sí |  |
| Llama-3.1-8B | `ultimo`, capa anidada | Δ | +0.1274 [+0.0919, +0.1651] | +0.1274 [+0.0899, +0.1647] | +0.0000 | sí | sí (por encima / por encima) |

En el Nivel C las dos implementaciones dan los mismos puntajes, bit a bit, en los dos modelos. Las 3752 puntuaciones de cada condición son idénticas y las 100 capas elegidas también, así que las tres cifras puntuales coinciden en todos sus decimales. Lo único que difiere son los límites de los intervalos, en la tercera cifra, porque cada implementación sortea sus remuestreos a su manera. En Qwen3-4B el intervalo de Δ es [+0.1198, +0.1867] con `probe.py` y [+0.1211, +0.1871] con la referencia; en Llama-3.1-8B, [+0.0919, +0.1651] y [+0.0899, +0.1647]. Los cuatro quedan lejos de cero.

Esa identidad tiene una lectura que conviene tener presente. La regla del Nivel C (§4) fija el mismo probe que usa `probe.py`: StandardScaler y regresión logística de sklearn con C = 1. La identidad bit a bit indica además que la referencia corrió con el mismo BLAS, presumiblemente en este mismo Mac. Que los puntajes salgan idénticos dice que las dos implementaciones arman las mismas particiones, eligen las mismas capas y promedian igual. No es una comprobación independiente del ajuste numérico, porque las dos llaman al mismo solver. En el Nivel A, en cambio, la referencia usa un solver propio, y por eso allí las cifras difieren en la tercera o cuarta decimal.

La segunda implementación del Nivel C, la del agente independiente, da para Qwen3-4B 0.8321, 0.6786 y Δ = +0.1535 [+0.1210, +0.1871] (`nivel_c/segunda_implementacion/resultado_c1.json`, abierto después de la corrida). Las tres implementaciones quedan a menos de 0.0001 entre sí.

### Capas frente a la referencia

| Modelo | Capas iguales, completo | Capas iguales, solo_lean | Particiones con capa distinta (semilla, partición: `probe.py` / referencia) |
|---|---|---|---|
| Qwen3-4B | 25 de 25 | 25 de 25 | ninguna |
| Llama-3.1-8B | 25 de 25 | 25 de 25 | ninguna |

### Capas elegidas por `probe.py`

| Modelo | Condición | Semilla 0 | Semilla 1 | Semilla 2 | Semilla 3 | Semilla 4 |
|---|---|---|---|---|---|---|
| Qwen3-4B | completo | 24, 36, 31, 31, 32 | 36, 28, 32, 31, 36 | 35, 26, 36, 31, 31 | 31, 36, 31, 31, 24 | 24, 36, 25, 36, 31 |
| Qwen3-4B | solo_lean | 26, 32, 29, 27, 35 | 27, 26, 27, 33, 31 | 25, 27, 30, 36, 31 | 29, 21, 31, 30, 30 | 35, 24, 27, 31, 28 |
| Llama-3.1-8B | completo | 15, 16, 32, 22, 23 | 14, 17, 16, 15, 28 | 23, 16, 21, 15, 17 | 26, 17, 21, 18, 15 | 15, 17, 15, 17, 15 |
| Llama-3.1-8B | solo_lean | 14, 23, 22, 30, 15 | 14, 22, 14, 16, 14 | 18, 22, 14, 20, 23 | 22, 18, 14, 5, 22 | 23, 15, 14, 18, 14 |

### Correlación fila a fila de los puntajes (3752 filas)

| Modelo | Lectura | Condición | Pearson | Spearman | Mayor diferencia absoluta | `y` idéntico |
|---|---|---|---|---|---|---|
| Qwen3-4B | `ultimo`, capa anidada | completo | 1.0000 | 1.0000 | 0.000 | sí |
| Qwen3-4B | `ultimo`, capa anidada | solo_lean | 1.0000 | 1.0000 | 0.000 | sí |
| Llama-3.1-8B | `ultimo`, capa anidada | completo | 1.0000 | 1.0000 | 0.000 | sí |
| Llama-3.1-8B | `ultimo`, capa anidada | solo_lean | 1.0000 | 1.0000 | 0.000 | sí |

### Barajadas

| Modelo | Capas | Media de la AUROC barajada por capa | Rango de los quince valores |
|---|---|---|---|
| Qwen3-4B | 12, 24, 36 | 0.501, 0.499, 0.506 | 0.484 a 0.516 |
| Llama-3.1-8B | 10, 21, 32 | 0.498, 0.503, 0.508 | 0.487 a 0.520 |

Con 3752 filas las barajadas quedan mucho más cerca de 0.5 que en el Nivel A.

## Nivel B: no se corrió

La cifra que el artículo reporta en el Nivel B es la diferencia de AUROC *pareada*. Es la probabilidad de que la variante fiel de un par puntúe por encima de su gemela infiel, promediada dentro del origen y luego entre orígenes, con bootstrap de orígenes y particiones agrupadas por archivo fuente (`nivel_b/regla_borrador.md` y sus precisiones del 5 nov). `probe.py` no la calcula. Su `auroc` es la AUROC global sobre filas, y `ic_bootstrap` y `diferencia_pareada` remuestrean un solo vector de grupos, estratificado por clase.

Para compararlo harían falta tres piezas que hoy no existen en `probe.py`:

1. Una función de AUROC pareada dentro del par, con empates en ½ y promedio por origen.
2. Un bootstrap de orígenes, sin estratificar por clase, para la AUROC pareada y para la diferencia entre condiciones.
3. Dos vectores de grupo distintos: el archivo fuente para las particiones y el origen para el estadístico. `particiones_agrupadas` y `elegir_capa_anidada` reciben uno solo.

Escribir ese código es decisión de autoría de Carlos, así que no lo escribí.

## Lo que no se pudo comparar y por qué

- **Nivel B entero.** Por lo dicho arriba: estadístico pareado, bootstrap de orígenes y dos agrupamientos. Tampoco la intervención, los controles de superficie ni las tripletas.
- **Nivel A, veredicto del prerregistro.** Las 1000 permutaciones, la corrección de Holm, el control apilado, la sensibilidad sin las 44 filas dudosas y el metaanálisis no están en `probe.py`.
- **Nivel A, controles nulos.** `qwen3_4b_aleatorio` y los embeddings bge-m3 no estaban en la lista del encargo y no se corrieron.
- **Nivel A, variantes con permutaciones de la lectura (i).** `referencia/v2_resultados_{olmo2_7b,dsprover2_7b}_perm_i.json` no se abrieron. La comparación usó `v2_resultados_<modelo>.json`, como pide el encargo.
- **Nivel C, Δ dentro del mismo enunciado.** Necesita una AUROC dentro de grupo que `probe.py` no tiene.
- **Nivel C, transferencia desde CriticLeanBench.** Necesita elegir la capa en un conjunto, ajustar ahí y puntuar otro. `main` no lo hace y armarlo sería lógica nueva.
- **Nivel C, controles.** Apilado, n-gramas de los dos textos, NL desemparejado, P(Yes), las 20 permutaciones de cordura y la posición `media_lean`, que la regla deja como secundaria y el artículo no reporta.
- **Curvas por capa, superficie y P(Yes) de los otros siete modelos del Nivel A.** `main` entero solo se corrió para Qwen3-4B.

## Tiempo y entorno

### Nivel A

| Modelo | Forma de las activaciones | Lectura (i), s | Lectura (ii), s | Barajadas, s | Salidas escritas | Referencia abierta |
|---|---|---|---|---|---|---|
| Qwen3-4B | (500, 37, 2560), float16 | 154 | 5 | 2 | 22:11:11 | 22:12:03 |
| OLMo-2-7B | (500, 33, 4096), float16 | 789 | 8 | 14 | 22:24:52 | 22:26:55 |
| Gemma-3-4B | (500, 35, 2560), float32 | 386 | 7 | 10 | 22:18:05 | 22:26:55 |
| Llama-3.1-8B | (500, 33, 4096), float16 | 948 | 8 | 16 | 22:27:34 | 22:37:21 |
| DeepSeek-Prover-V2-7B | (500, 31, 4096), float16 | 727 | 7 | 15 | 22:23:52 | 22:26:55 |
| Goedel-Prover-V2-8B | (500, 37, 4096), float16 | 1522 | 23 | 13 | 22:44:06 | 22:48:08 |
| Kimina-7B | (500, 29, 3584), float16 | 870 | 22 | 14 | 22:39:01 | 22:48:08 |
| Qwen3-8B | (500, 37, 4096), float16 | 1402 | 21 | 13 | 22:48:51 | 22:48:53 |

Los segundos son de reloj dentro de cada proceso. Qwen3-4B corrió solo; los otros siete corrieron de a cuatro, y desde las 22:15 compartieron la máquina con cinco procesos del Nivel C, así que sus tiempos no miden el costo aislado. La columna «Referencia abierta» es la hora en que `comparar_nivel_a.py` leyó el JSON y los `.npz` de la referencia de ese modelo.

### Nivel C

| Modelo | Forma de las activaciones | Lectura (i), s | Barajadas, s | Salidas escritas | Referencia abierta |
|---|---|---|---|---|---|
| Qwen3-4B | (3752, 37, 2560), float16 | 13262 | 92 | 23:01:01 | 23:02:06 |
| Llama-3.1-8B | (3752, 33, 4096), float16 | 18119 | 114 | 00:03:36 | 00:03:43 |

En el Nivel C la columna de la lectura suma los segundos de CPU de las diez corridas de `elegir_capa_anidada`, que fueron en procesos separados, cinco a la vez.

**Total.** El cómputo duró 1 h 56 min de reloj, de las 22:08 a las 00:04. En tiempo de proceso fueron unas 11.6 horas: 1.9 del Nivel A (de 161 s en Qwen3-4B a 1560 s en Goedel), 0.9 del `main` entero y 8.7 de las veinte corridas anidadas del Nivel C (13262 s en Qwen3-4B y 18119 s en Llama-3.1-8B).

### Entorno

- Mac de Carlos: macOS 26.7.3, arm64, 10 núcleos, 24 GB. `biblioteca/.venv`: Python 3.13.13, numpy 2.5.4 con BLAS Accelerate, scikit-learn 1.9.1, **scipy 1.18.1**, pyarrow 26.0.1.
- `ps` a las 22:06 no mostró procesos pesados de Carlos, así que no hizo falta `nice`.
- **Hilos.** Un ajuste de `_ajustar_y_puntuar` con 360 filas y 2560 dimensiones tarda de 0.012 a 0.018 s con los hilos por defecto y lo mismo con `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1`, con puntajes idénticos (`cronometro_defecto.log`, `cronometro_un_hilo.log`). Con 3003 filas tarda cerca de 1 s en las dos condiciones. En este Mac no aparece la diferencia de 40 veces de la máquina Linux. Se corrió con un hilo por proceso y varios procesos a la vez.
- A las 22:37 el Mac estaba con batería, que bajó hasta 59 %. Carlos lo conectó hacia las 23:10 y no se interrumpió nada.

## Cómo se corrió

- **Regla antes de correr.** La regla del Nivel A y la del Nivel C están al final de `probes/BITACORA.md`, cada una escrita antes de su corrida, con los SHA de `probe.py` y de los archivos de orquestación. La entrada del Nivel A lleva la hora «22:10» y se escribió hacia las 22:08; la corrección está anotada en la entrada siguiente.
- **Orquestación.** `correr_nivel_a.py` (SHA-256 `c200d3b2…327e3d18`) y `correr_nivel_c.py` (`e9624ac9…7226f9ba`) llaman a las funciones de `probe.py` con los argumentos de `main`. El primero es una adaptación de `corrida_probe_2026-11-21/correr_lecturas.py`. El segundo solo carga los datos con `probe.cargar`, sin `subconjunto` ni `_verificar_conteos`, y llama a `elegir_capa_anidada`, `ic_bootstrap`, `diferencia_pareada` y `control_barajadas`. `correr_main.py` (`ab3699da…4b205429d9`) llama a `probe.main`.
- **Orden de lectura.** Para cada modelo, los resultados de la referencia se abrieron después de que sus salidas de `probe.py` estuvieran en disco. Las dos horas están en cada `comparacion.json`. Los comparadores (`comparar_nivel_a.py`, `comparar_nivel_c.py`) se niegan a abrir la referencia si faltan salidas.
- **Código que no se leyó.** `referencia/probe_referencia.py`, `referencia/prerregistro_v2_analisis.py` y los scripts de análisis de `nivel_b/` y `nivel_c/`, incluida la segunda implementación. Sí se leyeron las reglas, los manifiestos, los `meta.json`, y después de cada corrida los JSON y `.npz` de resultados.
- **Lo que se vio antes de tiempo.** Hacia las 22:12, al leer el artículo para identificar las cifras de los Niveles B y C, vi la tabla del Nivel A con los cuatro modelos prerregistrados y las Δ de los modelos de descubrimiento. A esa hora la cola del Nivel A corría desde las 22:11:21 con el orquestador ya fijado y solo estaban en disco las lecturas (ii) de cuatro modelos. Del Nivel C vi la tabla del artículo antes de correr, porque había que leerla para saber cuál era la cifra principal. De Qwen3-4B en el Nivel A ya se conocían las cifras por el informe del 21 nov. Todo está anotado en la bitácora antes de la corrida del Nivel C. Ningún parámetro se tocó.
- **Desviaciones.** Ninguna respecto de la regla. Dos decisiones de ejecución: los modelos corrieron en paralelo y no uno tras otro, y las diez corridas anidadas del Nivel C fueron en procesos separados. Ninguna cambia un número, porque cada proceso es independiente y determinista.

## Frase propuesta para el artículo (no aplicada)

El artículo y el README quedaron como estaban. Si Carlos decide actualizar los dos pasajes, propongo este texto, que dice lo que se comparó, nombra la excepción y conserva las frases ya confirmadas. Las cifras de Qwen3-4B son las que el artículo ya trae.

**Recuadro «Pending» de la sección 3, en inglés.**

> All numbers in this version come from the reference implementation. By the rule of the project, they become findings only after comparison with the first author's own hand-written implementation (`probe.py`). That comparison has been run for the gap Δ at Level A, in the eight models and under both readouts, and at Level C, in the two models. In every case both AUROCs and the gap agree with the reference within 0.005. The interval of the gap falls on the same side of zero in both implementations, or includes zero in both, in every case but one. The exception is Qwen3-8B under readout (i), where `probe.py` gives +0.046 [0.002, 0.091] and the reference +0.043 [−0.004, 0.088]. In Qwen3-4B at Level A, `probe.py` gives Δ = +0.088 [0.042, 0.136] under readout (i) and +0.096 [0.055, 0.135] under readout (ii), against +0.091 and +0.095 from the reference. `probe.py` runs no permutation test and computes no control, so the comparison does not cover the decision of the preregistration, the meta-analysis or the controls of any level. Level B has not been compared, because `probe.py` does not compute its paired AUROC. The same holds for the within-statement gap and the transfer of Level C. Those numbers remain preliminary. Level C also has a second implementation, written by a separate coding agent with no access to the first and starting from the same extracted activations. It reproduces the main result of that level.

**Recuadro «Pendiente», en español.**

> Todas las cifras de esta versión provienen de la implementación de referencia. Por la regla del proyecto, pasan a ser hallazgos solo después de compararlas con la implementación escrita a mano por el primer autor (`probe.py`). Esa comparación ya se hizo para la brecha Δ en el Nivel A, en los ocho modelos y con las dos lecturas, y en el Nivel C, en los dos modelos. En todos los casos las dos AUROC y la brecha coinciden con la referencia dentro de 0.005. El intervalo de la brecha cae del mismo lado del cero en las dos implementaciones, o lo incluye en las dos, en todos los casos menos uno. La excepción es Qwen3-8B en la lectura (i), donde `probe.py` da +0.046 [0.002, 0.091] y la referencia +0.043 [−0.004, 0.088]. En Qwen3-4B, en el Nivel A, `probe.py` da Δ = +0.088 [0.042, 0.136] en la lectura (i) y +0.096 [0.055, 0.135] en la lectura (ii), frente a +0.091 y +0.095 de la referencia. `probe.py` no hace pruebas de permutación ni calcula ningún control, así que la comparación no cubre la decisión del prerregistro, el metaanálisis ni los controles de ningún nivel. El Nivel B no se ha comparado, porque `probe.py` no calcula su AUROC pareada. Lo mismo vale para la brecha dentro del mismo enunciado y la transferencia del Nivel C. Esas cifras siguen siendo preliminares. El Nivel C tiene además una segunda implementación, escrita por otro agente de programación sin acceso a la primera y a partir de las mismas activaciones extraídas. Reproduce el resultado principal de ese nivel.

La última parte del recuadro en español debe conservar la redacción que ya tiene `main_es.tex`; aquí la parafraseo.

**Párrafo «Use of AI tools», la parte que cambia.**

> For the gap at Level A, in the eight models, and at Level C, in the two models, that comparison has been run and the two implementations agree within 0.005. They also agree on the side of zero on which the interval falls, except for Qwen3-8B under readout (i). An AI assistant executed `probe.py`, unchanged. For Level B and for the controls of every level the comparison is pending.

> Para la brecha en el Nivel A, en los ocho modelos, y en el Nivel C, en los dos modelos, esa comparación ya se hizo y las dos implementaciones coinciden dentro de 0.005. También coinciden en el lado del cero en que cae el intervalo, salvo en Qwen3-8B con la lectura (i). Un asistente de IA ejecutó `probe.py` sin modificarlo. Para el Nivel B y para los controles de todos los niveles la comparación sigue pendiente.

Tres cosas que Carlos tendría que decidir antes de aplicar este texto:

1. Si la excepción de Qwen3-8B se reporta así o si antes quiere mirar la causa en el código de la referencia.
2. Si la sección «A later exploratory model», que da +0.043 [−0.004, 0.088] para Qwen3-8B en la lectura (i), lleva una nota con la cifra de `probe.py`.
3. Si el ejemplo de Qwen3-4B conserva las cifras de la corrida Linux o pasa a las del Mac.

Cambio de plan del 22 nov a las 23:10: el repositorio publica solo `paper_adecuacion/v6_retorica`. Si Carlos aprueba el texto, los pasajes se registran como tanda nueva en `v5_causal/aplica_v5.py`, después se corre `python3 aplica_v6.py ../v5_causal .` dentro de `v6_retorica`, se compilan ahí los dos PDF y se copian a `faithfulness/paper_adecuacion/v6_retorica` solo `main_en.tex`, `main_es.tex`, los dos PDF y los `.bbl`. En el README se toca únicamente la sección «Status». En `verifica_v5.py` habrá que poner en `FORMULAS_NUEVAS["\\D"]` el número de Δ nuevas en modo matemático. Hoy espera 2, y con los pasajes editados a mano el 22 nov ya hay 3, así que `verifica_v5.py` falla desde antes de esta corrida. En el .tex, `probe.py` va como `\vr{probe.py}`, Δ como `$\D$` y los intervalos con `\ic{}{}`.

No se dejó bloque de `git add`, `git commit` y `git push`, porque nada se copió a `faithfulness/`.

## Archivos

Todo está en `probes/corrida_probe_todo_2026-11-22/`.

- `salida/nivel_a/<modelo>/`: `datos.json`, `lectura_i.json`, `lectura_ii.json`, `barajadas.json`, los puntajes (`puntajes_i.npz`, `puntajes_ii.npz` y las diez corridas anidadas por separado) y `comparacion.json`.
- `salida/nivel_a/diagnostico_ic.json`: el bootstrap de `probe.py` sobre los puntajes de la referencia.
- `salida/nivel_c/<carpeta>/`: lo mismo para la prueba central del Nivel C.
- `main_qwen3_4b/`: el informe y las figuras del `main` entero.
- Orquestación y comparación: `correr_nivel_a.py`, `correr_nivel_c.py`, `correr_main.py`, `comparar_nivel_a.py`, `comparar_nivel_c.py`, `diagnostico_ic.py`, las dos colas y sus registros.
- Este informe se arma con `armar_informe.py` a partir de `informe_plantilla.md` y de las tablas que `tablas_informe.py` saca de los `comparacion.json`. Ninguna cifra de las tablas generadas se escribió a mano.

Autoría del código de `probe.py`: Carlos. Corrida: Claude Code en el Mac de Carlos, 22 nov 2026.
