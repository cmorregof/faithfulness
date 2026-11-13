# Nivel C, C1: segunda implementación independiente (Qwen3-4B, ProofNetVerif)

Implementación escrita desde cero a partir de `regla_borrador.md` (§3, §4 y C1-dentro), sin leer `probe_c.py`, `probes/referencia/` ni `probes/probe.py`. Código: `c1_independiente.py`; resultado: `resultado_c1.json` (+ `resultado_c1.npz` con los OOF por semilla); bitácora: `corrida_c1.log`.

## Diseño implementado
- 3 752 filas, 1 142 positivas, 361 grupos (17 solo positivas, 127 solo negativas, 217 mixtos). Posición «ultimo»; condiciones «completo» y «solo_lean»; capas 0–36 (embeddings + 36).
- Probe: StandardScaler ajustado en el entrenamiento + LogisticRegression (L2, C = 1, lbfgs, max_iter = 20 000; máximo de iteraciones observado: 555, sin avisos de no convergencia).
- Particiones externas: StratifiedGroupKFold(5, shuffle=True, random_state=s), s = 0–4, por `grupo`; idénticas en ambas condiciones (dependen solo de etiqueta, grupo y semilla). Comprobado: cada fila sale una vez en test y ningún grupo cruza train/test.
- Capa: CV anidada en cada fold externo con StratifiedGroupKFold(5, shuffle=True, misma semilla) sobre el entrenamiento; criterio = AUROC de los OOF internos concatenados; empate → capa más baja. Por separado en cada condición.
- Puntaje por fila: `predict_proba` OOF promediado entre las 5 semillas.
- IC 95 %: bootstrap percentil de grupos, 2 000 remuestreos, `np.random.default_rng(0)`, estratificado por tipo de grupo (en cada estrato se remuestrean con reemplazo tantos grupos como hay).
- C1-dentro: fracción de pares (positiva, negativa) del mismo grupo, agregada sobre todos los pares de los 217 grupos mixtos (7 568 pares), empates ½; IC por bootstrap de grupos mixtos (2 000, semilla 0).
- Cómputo: CPU, 2 procesos, `nice -n 10`, 14 021 s (3,9 h). Prueba previa de punta a punta con capas {0, 18, 36} y semillas {0, 1}.

## Resultados (escritos antes de abrir los de la primera implementación)

| | AUROC completo | AUROC solo_lean | Δ | IC 95 % de Δ |
|---|---|---|---|---|
| **C1 principal** | 0,8321 [0,8074; 0,8553] | 0,6786 [0,6458; 0,7114] | **+0,1535** | **[+0,1210; +0,1871]** |
| **C1-dentro de grupo** | 0,8524 [0,8268; 0,8785] | 0,6761 [0,6390; 0,7110] | **+0,1763** | **[+0,1412; +0,2135]** |

- EE bootstrap de Δ: 0,0166.
- Por semilla (AUROC con los OOF de una sola semilla): Δ = 0,1439; 0,1530; 0,1627; 0,1432; 0,1554. Media 0,1517, DE 0,0082, rango [0,1432; 0,1627]. (AUROC completo por semilla: 0,809; 0,810; 0,822; 0,811; 0,802. solo_lean: 0,665; 0,657; 0,659; 0,668; 0,646.)
- Capas elegidas (25 folds × semilla): completo mayoritariamente 31 y 36 (rango 24–36); solo_lean 21–36 (moda 27/31).
- Sensibilidad (no es la regla): promediar logits en vez de probabilidades da Δ = 0,1503 [0,1189; 0,1831] y Δ_dentro = 0,1813 [0,1453; 0,2185]. La media de AUROC por grupo (en vez de agregar pares) da Δ_dentro = 0,2041.

**Lectura según la regla:** el IC de Δ queda entero por encima de 0 → C1 **positivo**: las activaciones de «completo» separan adecuadas de inadecuadas mejor que «solo_lean». C1-dentro también positivo (IC > 0): dentro de un mismo enunciado, la información adicional es decodificable linealmente. Valen los límites de §9 (contaminación, ruido de etiqueta, negativos no compilables).

## Comparación con la primera implementación
(Sección añadida después de escribir lo anterior; ver abajo.)

Abierto `resultados/resultados_c_qwen3_4b.json` solo después de escribir las cifras anteriores.

| Cifra | 1.ª implementación | 2.ª (esta) | Diferencia |
|---|---|---|---|
| AUROC completo | 0,83205 [0,80734; 0,85517] | 0,83210 [0,80741; 0,85528] | +0,00005 |
| AUROC solo_lean | 0,67848 [0,64588; 0,71125] | 0,67856 [0,64582; 0,71139] | +0,00008 |
| **Δ principal** | **0,15357 [0,12112; 0,18711]** | **0,15354 [0,12102; 0,18714]** | −0,00003 |
| AUROC_dentro completo | 0,85254 | 0,85240 | −0,00013 |
| AUROC_dentro solo_lean | 0,67600 | 0,67614 | +0,00013 |
| **Δ dentro** | **0,17653 [0,14143; 0,21350]** | **0,17627 [0,14120; 0,21348]** | −0,00026 |
| Δ semilla 0–4 | 0,14393; 0,15295; 0,16258; 0,14319; 0,15519 | 0,14392; 0,15299; 0,16268; 0,14325; 0,15544 | ≤ 0,00025 |

**Veredicto: coinciden.** Las diferencias (≤ 3·10⁻⁴) son unas 30 veces menores que la DE de Δ entre semillas (0,008) y unas 60 veces menores que el EE bootstrap (0,017). Los IC coinciden hasta el tercer decimal, lo que indica que ambas usan las mismas particiones, la misma estratificación del bootstrap y la misma definición de C1-dentro (pares agregados, no media por grupo). Ambas dan C1 positivo y C1-dentro positivo.

Origen probable de las diferencias residuales: tolerancia de lbfgs / precisión numérica (aquí float64 y max_iter = 20 000), o que la otra promedie otro tipo de puntaje; no lo comprobé porque no leí `probe_c.py`. La sensibilidad a promediar logits (Δ = 0,1503) es mayor que la discrepancia observada, así que lo más probable es que ambas promedien probabilidades.

Puntos de diseño que la regla no fija y que tuve que decidir: (1) escala del puntaje que se promedia entre semillas (probabilidades); (2) AUROC interno sobre los OOF internos concatenados, no la media por fold; (3) AUROC_dentro agregado sobre pares, no la media por grupo (la media por grupo da 0,204); (4) orden de estratos y de remuestreo en el bootstrap (afecta al IC solo en el cuarto decimal); (5) `shuffle=True` también en la CV interna. Ninguno cambia la decisión.

Nota de proceso: al comprobar procesos en marcha vi en `ps` la línea de comando de otra sesión que importa `probe_c` para calcular subconjuntos. No mostraba cifras ni la lógica de C1, y no la usé.
