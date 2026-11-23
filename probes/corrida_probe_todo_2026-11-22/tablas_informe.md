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

### Capas elegidas por `probe.py` en la lectura (i), por semilla (cinco particiones externas cada una)

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

### Correlación fila a fila (450 filas)

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

### Barajadas

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

### Tiempos

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

## Nivel C

| Modelo | Lectura | Cantidad | `probe.py` | Referencia | Diferencia | ¿Dentro de 0.005? | ¿Misma decisión? |
|---|---|---|---|---|---|---|---|
| Qwen3-4B | (i) | AUROC(completo) | 0.8320 [0.8074, 0.8546] | 0.8320 [0.8073, 0.8552] | +0.0000 | sí |  |
| Qwen3-4B | (i) | AUROC(solo_lean) | 0.6785 [0.6463, 0.7112] | 0.6785 [0.6459, 0.7112] | +0.0000 | sí |  |
| Qwen3-4B | (i) | Δ | +0.1536 [+0.1198, +0.1867] | +0.1536 [+0.1211, +0.1871] | +0.0000 | sí | sí (por encima / por encima) |
| Llama-3.1-8B | | sin comparar | | | | | |

### Capas frente a la referencia

| Modelo | Capas iguales, completo | Capas iguales, solo_lean | Particiones con capa distinta (semilla, partición: `probe.py` / referencia) |
|---|---|---|---|
| Qwen3-4B | 25 de 25 | 25 de 25 | ninguna |

### Capas elegidas por `probe.py`

| Modelo | Condición | Semilla 0 | Semilla 1 | Semilla 2 | Semilla 3 | Semilla 4 |
|---|---|---|---|---|---|---|
| Qwen3-4B | completo | 24, 36, 31, 31, 32 | 36, 28, 32, 31, 36 | 35, 26, 36, 31, 31 | 31, 36, 31, 31, 24 | 24, 36, 25, 36, 31 |
| Qwen3-4B | solo_lean | 26, 32, 29, 27, 35 | 27, 26, 27, 33, 31 | 25, 27, 30, 36, 31 | 29, 21, 31, 30, 30 | 35, 24, 27, 31, 28 |

### Correlación fila a fila (3752 filas)

| Modelo | Lectura | Condición | Pearson | Spearman | Mayor diferencia absoluta | `y` idéntico |
|---|---|---|---|---|---|---|
| Qwen3-4B | (i) | completo | 1.0000 | 1.0000 | 0.000 | sí |
| Qwen3-4B | (i) | solo_lean | 1.0000 | 1.0000 | 0.000 | sí |

### Barajadas

| Modelo | Capas | Media de la AUROC barajada por capa | Rango de los quince valores |
|---|---|---|---|
| Qwen3-4B | 12, 24, 36 | 0.501, 0.499, 0.506 | 0.484 a 0.516 |

### Tiempos

| Modelo | Forma de las activaciones | Lectura (i), s | Barajadas, s | Salidas escritas | Referencia abierta |
|---|---|---|---|---|---|
| Qwen3-4B | (3752, 37, 2560), float16 | 13262 | 92 | 23:01:01 | 23:02:06 |
