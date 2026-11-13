# Nivel B: precisiones a `regla_borrador.md` para el análisis pareado de los 377 pares (5 nov 2026)

**Estado:** escrito por la sesión madre antes de cualquier resultado del análisis pareado del Nivel B. A esta hora no existe ninguna activación analizada; la extracción está en curso y nadie la ha mirado. **Pendiente de aprobación de Carlos.**

**Regla base:** `probes/nivel_b/regla_borrador.md`, SHA-256 `d2236454f1bc81f9f667359a61de1604aff0119c2bec208ada9e5b7850120559`.
- Su última modificación es del 4 nov a las 17:34. Es anterior a la certificación (5 nov, 06:07) y a la extracción (5 nov, 22:12).
- Incluye las dos pasadas del Fable, ya aplicadas en `analizar_pares.py`.

**Implementación:** `probes/nivel_b/analizar_pares.py`.
- SHA-256 al momento de escribir esto: ver la bitácora.
- Único cambio de hoy: acepta un índice filtrado.

## Precisiones que la regla no fijaba o que cambiaron después

1. **Estatus.** El prompt de Carlos del 4 nov (22:29) dice que «los 893 pares son el lote de desarrollo».
   - Por eso este análisis se rotula como **desarrollo / exploratorio**.
   - La prueba principal del Nivel B es la de tripletas (`regla_v2_tripletas.md`).
   - El resultado se reporta con la decisión que da la regla, siempre con ese rótulo.

2. **Datos.** Se usan los pares certificados del lote registrado (`7dd3b052…`): 408 pares, parquet `fb80e4b2…`. Sobre ellos se aplica `datos/exclusiones_nivel_b.json`, fijado el 5 nov hacia las 06:3x, antes de cualquier activación del Nivel B.
   - **Principal:** 377 pares en 256 orígenes (índice `datos/pares_indice_principal.jsonl`).
   - **Se reportan aparte, como sensibilidad:**
     - con los 408 (índice completo);
     - sin los pares 4, 45, 56 y 203.
   - Las «B3 de caso base trivial» no están identificadas. No se forman a mano después de ver resultados. Si se identifican, tiene que ser por un criterio escrito antes.

3. **Tamaño.** 377 pares y 256 orígenes caen en la rama **«potencia reducida»** (≥ 200 pares, < 300 orígenes). Un positivo vale con ese rótulo. Un nulo se reporta con la cota superior del IC.

4. **Compuerta de superficie.** Sobre los certificados da 0,706, con exceso 0,081; no pasa con ninguno de los dos criterios.
   - Carlos la declaró **exploratoria** (prompt del 4 nov, 22:29), así que **no bloquea**.
   - El informe declara su valor y el nivel absoluto de solo_lean como techo de la diferencia (§«Cambios del revisor», 2.ª pasada, punto 1).

5. **Condición del control 6** (superficie cruzada NL–Lean). Se mantiene como la dejó el Fable: si el IC de completo − cruzada queda entero por debajo de 0, la decisión es «NULO (condición 6)».

6. **Elecciones que la regla dejaba abiertas.** Quedan como están implementadas:
   - sin los pares con reglas de huella (D2, D3, D6, D7);
   - 2 pares por origen como máximo;
   - permutaciones: 100 intercambios de roles dentro del par, con las particiones de la semilla 0 y la selección de capa incluida;
   - particiones agrupadas por archivo fuente;
   - bootstrap por origen (principal) y por archivo (sensibilidad);
   - réplicas (Kimina, Goedel): no se corren en este análisis.

7. **`verdad_variante` para el control 8** (fidelidad ≠ verdad). Se aplica la corrección del §4 de `revision_confirmacion_certificados_opus.md` antes de calcularlo:
   - los 7 pares de nivel 1 son variantes falsas;
   - las B4∘D4c son verdaderas si el original lo es.

   Si no se aplica, el control 8 se reporta con la advertencia.

8. **Modelo y cómputo.** Qwen3-4B; posición «ultimo» como principal y «media_lean» como secundaria.
   - Se corre con `--jobs 2` mientras haya permutaciones del Nivel A en CPU.
   - Si no termina hoy, sigue sin cambiar nada.

9. **Añadida por Carlos (2026-11-05 22:44 -05, antes de cualquier resultado).** Se reporta siempre completo − superficie cruzada NL–Lean, con su IC. Solo si ese IC queda entero por encima de 0 se puede escribir que el efecto va «más allá de la superficie»; si no, se escribe «no distinguible de la superficie con estos pares». Es secundaria y no cambia la decisión principal.
