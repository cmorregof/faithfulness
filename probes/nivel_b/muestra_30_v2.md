# Muestra v2 (Nivel B) — para revisión de Carlos

Generada por `probes/nivel_b/hacer_muestra_v2.py` (semilla 20261104) sobre `candidatos_v2.jsonl` (10658 candidatos; SHA-256 `f66e114cf33fed927ba8fa9b53092b0a615d2752a64d8a99b78a571663e8cecd`), **solo entre los 2222 candidatos del emparejamiento provisional** (1111 pares), estratificada por regla (29 reglas; 30 casos). **Nada está certificado.** La edición va entre ⟦ ⟧. Se omiten las líneas `import`. `muestra_30.md` (v1) queda intacta como histórico.

Para cada caso, tres preguntas: **(P0) ¿el Lean ORIGINAL es fiel al NL?** (premisa del diseño; si no, el par no vale); (P1) ¿la etiqueta esperada de la variante es correcta respecto al NL?; (P2) ¿la variante es un enunciado sensato (no un error de tipo disfrazado)? Anotar ✔/✘ y un comentario.

## 1. B2∘D8 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/211417:OeisA211417.general_divisibility` (archivo `OEIS/211417`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> Conjecture: "More generally, for r >= 1, we conjecture that there exists a constant D(r) such that
> D(r)*a(n)/Product_{i = 1..r, i coprime to 30} (30*n - i) is integral for all n."
> - _Peter Bala_, Aug 28 2025
> 
> This generalizes `thirty_mul_sub_one_dvd_a` (the $r = 1$ case where $D(1) = 1$).
> 
> **Proof sketch** (kernel-checked development at the `formal_proof` permalink below, which
> proves the non-vacuous form with the explicit positive witness $D = (r!)^{r^2}$):
> Legendre-valuation analysis of the Landau step function
> $\Delta(x) = \lfloor 30x \rfloor + \lfloor x \rfloor - \lfloor 15x \rfloor -
> \lfloor 10x \rfloor - \lfloor 6x \rfloor$, whose values lie in $\{0, 1\}$. Three
> ingredients: a unit-cla […]

**Lean original:**

```lean
theorem general_divisibility (r : ℕ) (hr : 1 ≤ r) :
    ∃ D : ℤ, 0 < D ∧ ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem general_divisibility (r : ℕ) (hr : ⟦0 < r⟧) :
    ∃ D : ℤ, 0 < D ∧ ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) := by
  sorry
```

**Variante infiel (B2∘D8; edición respecto a la base):**

```lean
theorem general_divisibility (r : ℕ) (hr : 0 < r) :
    ∃ D : ℤ, 0 ⟦≤⟧ D ∧ ∀ n : ℕ, (divisorProduct n r) ∣ (D * (a n : ℤ)) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 2. C2∘D1c (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Wikipedia/Bloch:Bloch.landauConstant_lower_bound` (archivo `Wikipedia/Bloch`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 9; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> It is proved in [Ya95] that the Landau constant is bounded below by $0.5 + 10 ^ {-335}$.

**Lean original:**

```lean
theorem landauConstant_lower_bound : 0.5 + 10 ^ (-335 : ℤ) ≤ landauConstant := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem landauConstant_lower_bound : ⟦landauConstant ≥ 0.5 + 10 ^ (-335 : ℤ)⟧ := by
  sorry
```

**Variante infiel (C2∘D1c; edición respecto a la base):**

```lean
theorem landauConstant_lower_bound : landauConstant ≥ 0.5 + ⟦11⟧ ^ (-335 : ℤ) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 3. D8 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/504:Erdos504.erdos_504.variants.endpoint` (archivo `ErdosProblems/504`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 2; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> **Erdős–Szekeres (1960).** For $n \ge 3$, also
> $\alpha_{2^n - 1} = \pi\left(1 - \frac{1}{n}\right)$.

**Lean original:**

```lean
theorem erdos_504.variants.endpoint {n : ℕ} (hn : 3 ≤ n) :
    minimaxAngle (2 ^ n - 1) = (1 - 1 / (n : ℝ)) * π := by
  sorry
```

**Variante (D8; edición respecto al original):**

```lean
theorem erdos_504.variants.endpoint {n : ℕ} (hn : ⟦2 < n⟧) :
    minimaxAngle (2 ^ n - 1) = (1 - 1 / (n : ℝ)) * π := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 4. C3∘D8 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/384:Erdos384.erdos_384` (archivo `ErdosProblems/384`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> If $1<k<n-1$ then $\binom{n}{k}$ is divisible by a prime $p\leq n/2$ (except
> $\binom{7}{3}=\binom{7}{4}=5\cdot 7$).
> 
> A conjecture of Erdős and Selfridge [ErGr80]. Proved by Ecklund [Ec69], who made the stronger
> conjecture that whenever $n>k^2$ the binomial coefficient $\binom{n}{k}$ is divisible by a prime
> $p<n/k$. Discussed in problem B31 and B33 of Guy's collection [Gu04]. Stronger forms of this
> conjecture are [1094](https://www.erdosproblems.com/1094) and
> [1095](https://www.erdosproblems.com/1095).
> 
> Ecklund's theorem is stated for $n \geq 2k$ with the single exception $\binom{7}{3}$; by the
> symmetry $\binom{n}{k} = \binom{n}{n-k}$ this is the form above, where $\binom{7}{4}$ is the
> second […]

**Lean original:**

```lean
theorem erdos_384 (n k : ℕ) (hk : 1 < k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3))
    (h₄ : (n, k) ≠ (7, 4)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem erdos_384 (n k : ℕ) (hk : ⟦2 ≤ k⟧) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3))
    (h₄ : (n, k) ≠ (7, 4)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  sorry
```

**Variante infiel (C3∘D8; edición respecto a la base):**

```lean
theorem erdos_384 (n k : ℕ) (hk : 2 ≤ k) (hkn : k < n - 1) (h₃ : (n, k) ≠ (7, 3))
    (h₄ : (n, k) ≠ (7, 4)) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ⟦≥⟧ n := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 5. C3∘D1 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:WrittenOnTheWallII/GraphConjecture16:WrittenOnTheWallII.GraphConjecture16.example_L55` (archivo `WrittenOnTheWallII/GraphConjecture16`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 6; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> The invariant `b G` (largest induced bipartite subgraph size) is nonneg.

**Lean original:**

```lean
theorem example_L55 (G : SimpleGraph (Fin 3)) : 0 ≤ b G := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem example_L55 (G : SimpleGraph (Fin 3)) : ⟦b G ≥ 0⟧ := by
  sorry
```

**Variante infiel (C3∘D1; edición respecto a la base):**

```lean
theorem example_L55 (G : SimpleGraph (Fin 3)) : b G ⟦≤⟧ 0 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 6. B1∘D1 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/482:Erdos482.erdos_482.variants.binary_explicit` (archivo `ErdosProblems/482`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 13; respecto a la base fiel: 9; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> The explicit binary answer to the open-ended part [RaGi91], [St05]: for every normalized real
> $t \in [1, 2)$, the recurrence with coefficients $\alpha(t) = 2(t+1)/(t+2)$ and
> $\beta(t) = (t+2)/(t+1)$ reads off the binary digits of $t$, and those digits reconstruct $t$.
> Unlike `erdos_482.variants.stoll_general`, the coefficients are given, not merely shown to exist.

**Lean original:**

```lean
theorem erdos_482.variants.binary_explicit (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t < 2) :
    (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1 := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem erdos_482.variants.binary_explicit (t : ℝ) (ht1 : ⟦t ≥ 1⟧) (ht2 : t < 2) :
    (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1 := by
  sorry
```

**Variante infiel (B1∘D1; edición respecto a la base):**

```lean
theorem erdos_482.variants.binary_explicit (t : ℝ) (ht1 : t ≥ 1) (ht2 : t < 2)⟦ (ht_pos : 0 < t)⟧ :
    (∀ n, 1 ≤ n →
        stollBinary t (2 * n) - 2 * stollBinary t (2 * n - 2) = (binaryDigit t n).val) ∧
      Real.ofDigits (fun k ↦ binaryDigit t (k + 2)) = t - 1 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 7. D1c (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:OEIS/48153:OeisA48153.conjecture` (archivo `OEIS/48153`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 6; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> "Conjecture: $a(n) <= \frac{n^2-1}{2}$. - _Aspen A.M. Meissner_, Mar 06 2025"

**Lean original:**

```lean
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : a n ≤ (n ^ 2 - 1) / 2 := by
  sorry
```

**Variante (D1c; edición respecto al original):**

```lean
theorem conjecture (n : ℕ) (hn : 1 ≤ n) : ⟦(n ^ 2 - 1) / 2 ≥ a n⟧ := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 8. B4∘D4c (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Wikipedia/Conway99Graph:Conway99Graph.triangle_locallyLinear_and_nonEdgesAreDiagonals` (archivo `Wikipedia/Conway99Graph`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 14; respecto a la base fiel: 12; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> The triangle is an example with 3 vertices satisfying the condition.

**Lean original:**

```lean
theorem triangle_locallyLinear_and_nonEdgesAreDiagonals : (completeGraph (Fin 3)).LocallyLinear ∧
    NonEdgesAreDiagonals (completeGraph (Fin 3)) := by
  sorry
```

**Variante fiel (base D4c, la otra mitad del par; edición respecto al original):**

```lean
theorem triangle_locallyLinear_and_nonEdgesAreDiagonals : ⟦NonEdgesAreDiagonals (completeGraph (Fin 3)) ∧ (completeGraph (Fin 3)).LocallyLinear⟧ := by
  sorry
```

**Variante infiel (B4∘D4c; edición respecto a la base):**

```lean
theorem triangle_locallyLinear_and_nonEdgesAreDiagonals : ⟦NonEdgesAreDiagonals (completeGraph (Fin 3))⟧ := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 9. D4c (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `FormalMATH_lite[310]` (archivo `FormalMATH_lite[310]`; FormalMATH-Lite); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 24; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> A small appliances company makes toaster ovens and pizza cookers, and have noticed their customer base's purchasing habits give them the price-demand equations given below, where $p$ is the price and $x$ is the quantity of toaster ovens, $q$ is the price and $y$ is the quantity of pizza cookers. The Cost function is $C(x,y) = 160 + 12 \cdot x + 24 \cdot y$.
> 
> $p = 50 - 4 \cdot x + y$ and $q = 100 + x - 5 \cdot y$
> 
> 1. Construct the 2-product Revenue function, $R(x,y)$
> 2. Find $R(8,10)$
> 3. Construct the 2-product Profit function, $P(x,y)$
> 4. Find $P(8,10)$
>  Prove that the answer is: 1. $R(x,y)$ = $R(x,y)=50\cdot x+100\cdot y+2\cdot x\cdot y-4\cdot x^2-5\cdot y^2$
> 2. $R(8,10)$ = $804$
> 3. $P(x,y) […]

**Lean original:**

```lean
def R (x y : ℕ) := 50 * x + 100 * y + 2 * x * y - 4 * x ^ 2 - 5 * y ^ 2
def P (x y : ℕ) := 38 * x + 76 * y + 2 * x * y - 160 - 4 * x ^ 2 - 5 * y ^ 2

theorem u_math_371 : R 8 10 = 804 ∧ P 8 10 = 308 := by
```

**Variante (D4c; edición respecto al original):**

```lean
def R (x y : ℕ) := 50 * x + 100 * y + 2 * x * y - 4 * x ^ 2 - 5 * y ^ 2
def P (x y : ℕ) := 38 * x + 76 * y + 2 * x * y - 160 - 4 * x ^ 2 - 5 * y ^ 2

theorem u_math_371 : ⟦P 8 10 = 308 ∧ R 8 10 = 804⟧ := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 10. B2∘D1 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1168:Erdos1168.erdos_1168.variants.example_L69` (archivo `ErdosProblems/1168`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 12; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> `ℵ_ω < ℵ_{ω+1}`: the cardinal `ℵ_{ω+1}` is the successor of the singular `ℵ_ω`.

**Lean original:**

```lean
theorem example_L69 : ℵ_ ω < ℵ_ (ω + 1) := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem example_L69 : ⟦ℵ_ (ω + 1) > ℵ_ ω⟧ := by
  sorry
```

**Variante infiel (B2∘D1; edición respecto a la base):**

```lean
theorem example_L69 : ℵ_ (ω + 1) ⟦≥⟧ ℵ_ ω := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 11. B3∘D1c (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/400:Erdos400.erdos_400.variants.g_pos` (archivo `ErdosProblems/400`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 7; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> For $k \ge 2$, $g_k(n) > 0$. We show this by choosing $a = (n, 1, 0, \ldots, 0)$.

**Lean original:**

```lean
theorem erdos_400.variants.g_pos (k n : ℕ) (h: k ≥ 2) : 0 < g k n := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem erdos_400.variants.g_pos (k n : ℕ) (h: k ≥ 2) : ⟦g k n > 0⟧ := by
  sorry
```

**Variante infiel (B3∘D1c; edición respecto a la base):**

```lean
theorem erdos_400.variants.g_pos (k n : ℕ) (h: k ⟦>⟧ 2) : g k n > 0 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 12. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/3:Erdos3.erdos_3.variants.gowers` (archivo `ErdosProblems/3`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> For every $k \geq 3$ there is $c_k > 0$ such that $r_k(N) \ll_k N (\log \log N)^{-c_k}$.
> 
> Proved by Gowers [Go01].

**Lean original:**

```lean
theorem erdos_3.variants.gowers (k : ℕ) (hk : 3 ≤ k) : ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.log (Real.log N) ^ (-c) := by
  sorry
```

**Variante (D1; edición respecto al original):**

```lean
theorem erdos_3.variants.gowers (k : ℕ) (hk : ⟦k ≥ 3⟧) : ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪ fun N : ℕ ↦ (N : ℝ) * Real.log (Real.log N) ^ (-c) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 13. A1∘D1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Wikipedia/Falconer:Falconer.falconer_conjecture` (archivo `Wikipedia/Falconer`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 10; respecto a la base fiel: 10; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Falconer's distance set conjecture in dimension $d \ge 2$.
> 
> The hypothesis $2 \le d$ excludes a degenerate case: the conclusion is false for $d = 1$.
> The base-$7$ Cantor set $E = \{\sum_{n \ge 1} a_n 7^{-n} : a_n \in \{0, 1, 2\}\}$ is compact
> with $\dim_H E = \log 3 / \log 7 > 1/2$, but $E - E$ has digits in $\{-2, \dots, 2\}$, so
> after fixing $n$ digits it is covered by $5^n$ intervals of length $\frac{2}{3} 7^{-n}$ and is
> therefore null; its distance set is the image of $E - E$ under $|\cdot|$ and is null too.
> 
> This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
> proof.

**Lean original:**

```lean
theorem falconer_conjecture (d : ℕ) (h2d : 2 ≤ d) (E : Set <| ℝ^d) (hc : IsCompact E)
    (hd : d < 2 * dimH E) :
    0 < volume (image2 dist E E) := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem falconer_conjecture (d : ℕ) (h2d : ⟦d ≥ 2⟧) (E : Set <| ℝ^d) (hc : IsCompact E)
    (hd : d < 2 * dimH E) :
    0 < volume (image2 dist E E) := by
  sorry
```

**Variante infiel (A1∘D1; edición respecto a la base):**

```lean
theorem falconer_conjecture (d : ℕ)⟦⟧ (E : Set <| ℝ^d) (hc : IsCompact E)
    (hd : d < 2 * dimH E) :
    0 < volume (image2 dist E E) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 14. A3∘D1c (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/700:Erdos700.f_le` (archivo `ErdosProblems/700`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 7; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> `f n` is a lower bound: `f n ≤ gcd(n, C(n,k))` for every `1 < k ≤ n/2`.

**Lean original:**

```lean
theorem f_le (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    f n ≤ Nat.gcd n (n.choose k) := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem f_le (n k : ℕ) (h1 : 1 < k) (h2 : k ≤ n / 2) :
    ⟦Nat.gcd n (n.choose k) ≥ f n⟧ := by
  sorry
```

**Variante infiel (A3∘D1c; edición respecto a la base):**

```lean
theorem f_le (n k : ℕ) (h1 : 1 ⟦≤⟧ k) (h2 : k ≤ n / 2) :
    Nat.gcd n (n.choose k) ≥ f n := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 15. C3∘D1c (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:WrittenOnTheWallII/GraphConjecture13:WrittenOnTheWallII.GraphConjecture13.example_L54` (archivo `WrittenOnTheWallII/GraphConjecture13`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 6; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> The largest induced bipartite subgraph invariant `b G` is nonneg for any graph.

**Lean original:**

```lean
theorem example_L54 (G : SimpleGraph (Fin 3)) : 0 ≤ b G := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem example_L54 (G : SimpleGraph (Fin 3)) : ⟦b G ≥ 0⟧ := by
  sorry
```

**Variante infiel (C3∘D1c; edición respecto a la base):**

```lean
theorem example_L54 (G : SimpleGraph (Fin 3)) : b G ⟦≤⟧ 0 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 16. B1∘D4h (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[284]` (archivo `FormalMATH_lite[284]`; FormalMATH-Lite); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 25; respecto a la base fiel: 9; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> A 100 foot long moving walkway moves at a constant rate of 6 feet per second.  Al steps onto the start of the walkway and stands.  Bob steps onto the start of the walkway two seconds later and strolls forward along the walkway at a constant rate of 4 feet per second.  Two seconds after that, Cy reaches the start of the walkway and walks briskly forward beside the walkway at a constant rate of 8 feet per second.  At a certain time, one of these three persons is exactly halfway between the other two.  At that time, find the distance in feet between the start of the walkway and the middle person.
>  Prove that the answer is: 52

**Lean original:**

```lean
theorem aime_all_2007_I_2 (a b c t : ℝ) (ha : 0 ≤ t) (hb : 0 ≤ t - 2) (hc : 0 ≤ t - 4)
    (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c)
    (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    a = 52 := by
```

**Variante fiel (base D4h, la otra mitad del par; edición respecto al original):**

```lean
theorem aime_all_2007_I_2 (a b c t : ℝ) ⟦(hb : 0 ≤ t - 2) (ha : 0 ≤ t)⟧ (hc : 0 ≤ t - 4)
    (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c)
    (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2) :
    a = 52 := by
```

**Variante infiel (B1∘D4h; edición respecto a la base):**

```lean
theorem aime_all_2007_I_2 (a b c t : ℝ) (hb : 0 ≤ t - 2) (ha : 0 ≤ t) (hc : 0 ≤ t - 4)
    (hwalk : 6 * t = a) (hbob : 6 * (t - 2) + 4 * (t - 2) = b) (hcourier : 8 * (t - 4) = c)
    (hmidway : a = (b + c) / 2 ∨ b = (a + c) / 2 ∨ c = (a + b) / 2)⟦ (ha_pos : 0 < a)⟧ :
    a = 52 := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 17. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/905:Erdos905.erdos_905` (archivo `ErdosProblems/905`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 18; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> Every graph with $n$ vertices and $>n^2/4$ edges contains an edge which is in at least $n/6$
> triangles.
> 
> A conjecture of Bollobás and Erdős. This was proved independently by Edwards (unpublished) and
> Khadzhiivanov and Nikiforov [KhNi79].

**Lean original:**

```lean
theorem erdos_905 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : (n : ℝ) ^ 2 / 4 < (#G.edgeFinset : ℝ)) :
    ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ) := by
  sorry
```

**Variante (D1; edición respecto al original):**

```lean
theorem erdos_905 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ⟦(#G.edgeFinset : ℝ) > (n : ℝ) ^ 2 / 4⟧) :
    ∃ e ∈ G.edgeFinset, (n : ℝ) / 6 ≤ (#(G.trianglesContaining e) : ℝ) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 18. B3∘D1 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[10]` (archivo `FormalMATH_lite[10]`; FormalMATH-Lite); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> Proof: $\sum_{k = 0}^{\left[\frac{n - 1}{2}\right]}(-1)^k\mathrm{C}_{n + 1}^k\mathrm{C}_{2n - 2k - 1}^n=\frac{1}{2}n(n + 1)\ (n\geqslant1)$

**Lean original:**

```lean
open Nat

theorem algebra_385785 {n : ℕ} (hn : 1 ≤ n) :
    ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, (-1 : ℤ)^k * Nat.choose (n + 1) k * Nat.choose (2 * n - 2 * k - 1) n =
    (n * (n + 1)) / 2 := by
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
open Nat

theorem algebra_385785 {n : ℕ} (hn : ⟦n ≥ 1⟧) :
    ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, (-1 : ℤ)^k * Nat.choose (n + 1) k * Nat.choose (2 * n - 2 * k - 1) n =
    (n * (n + 1)) / 2 := by
```

**Variante infiel (B3∘D1; edición respecto a la base):**

```lean
open Nat

theorem algebra_385785 {n : ℕ} (hn : n ⟦>⟧ 1) :
    ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, (-1 : ℤ)^k * Nat.choose (n + 1) k * Nat.choose (2 * n - 2 * k - 1) n =
    (n * (n + 1)) / 2 := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 19. C2∘D1 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[86]` (archivo `FormalMATH_lite[86]`; FormalMATH-Lite); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 5; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> Let \(a, b, c, d>0\) and \(a + b + c + d = 1\). Prove that:
> \[
> \frac{1}{4a + 3b + c}+\frac{1}{3a + b + 4d}+\frac{1}{a + 4c + 3d}+\frac{1}{4b + 3c + d}\geqslant2.
> \]

**Lean original:**

```lean
theorem algebra_476989 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    2 ≤ 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) +
        1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) := by
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem algebra_476989 (a b c d : ℝ) (ha : ⟦a > 0⟧) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    2 ≤ 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) +
        1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) := by
```

**Variante infiel (C2∘D1; edición respecto a la base):**

```lean
theorem algebra_476989 (a b c d : ℝ) (ha : a > 0) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    ⟦3⟧ ≤ 1 / (4 * a + 3 * b + c) + 1 / (3 * a + b + 4 * d) +
        1 / (a + 4 * c + 3 * d) + 1 / (4 * b + 3 * c + d) := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 20. A1∘D4h (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1171:Erdos1171.erdos_1171.variants.mono_k` (archivo `ErdosProblems/1171`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 9; respecto a la base fiel: 9; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> `OrdinalMultiColorRamsey` is monotone in the number of non-zero colors:
> a witness for the `k`-color version yields one for any `j ≤ k`.

**Lean original:**

```lean
theorem mono_k {j k : ℕ} (hjk : j ≤ k)
    (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k) :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  sorry
```

**Variante fiel (base D4h, la otra mitad del par; edición respecto al original):**

```lean
theorem mono_k {j k : ℕ} ⟦(hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k)
    (hjk : j ≤ k)⟧ :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  sorry
```

**Variante infiel (A1∘D4h; edición respecto a la base):**

```lean
theorem mono_k {j k : ℕ} (hk : OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 k)⟦⟧ :
    OrdinalMultiColorRamsey (ω_ 1 ^ 2) (ω_ 1 * ω) 3 j := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 21. A2∘D1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:WrittenOnTheWallII/GraphConjecture144:WrittenOnTheWallII.GraphConjecture144.conjecture144` (archivo `WrittenOnTheWallII/GraphConjecture144`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 24; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> WOWII [Conjecture 144](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
> 
> For a simple connected graph $G$,
> $\mathrm{tree}(G) \ge \mathrm{girth}(G) - 1 + \mathrm{ecc}(\mathrm{Centers})$
> where $\mathrm{tree}(G)$ is the largest induced tree size, $\mathrm{girth}(G)$ is
> the length of the shortest cycle ($0$ if acyclic),
> $\mathrm{Centers} = G.\mathrm{center}$ is the set of vertices with minimum
> eccentricity (the center of $G$), and $\mathrm{ecc}(\mathrm{Centers})$ is the
> eccentricity of the center set — the maximum distance from any non-center
> vertex to the nearest center vertex.
> 
> **Proof sketch.** Let $g = \mathrm{girth}(G)$ and
> $e = \mathrm{ecc}(G, \mathrm{center}(G))$. The acyclic and $ […]

**Lean original:**

```lean
theorem conjecture144 (G : SimpleGraph α) (h : G.Connected) :
    (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) ≤ (largestInducedTreeSize G : ℝ) := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem conjecture144 (G : SimpleGraph α) (h : G.Connected) :
    ⟦(largestInducedTreeSize G : ℝ) ≥ (G.girth : ℝ) - 1 + (ecc G G.center : ℝ)⟧ := by
  sorry
```

**Variante infiel (A2∘D1; edición respecto a la base):**

```lean
theorem conjecture144 (G : SimpleGraph α) (h : G.Connected) :
    (largestInducedTreeSize G : ℝ) ⟦>⟧ (G.girth : ℝ) - 1 + (ecc G G.center : ℝ) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 22. D4h (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/1000:Erdos1000.erdos_1000.variants.not_tendsto_zero` (archivo `ErdosProblems/1000`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 14; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> Erdős [Er64b] proved that the limit of $\frac{\phi_A(k)}{n_k}$ as $k\to \infty$ cannot be $0$.

**Lean original:**

```lean
theorem erdos_1000.variants.not_tendsto_zero (n : ℕ → ℕ) (hn : StrictMono n) (hn0 : 0 < n 0) :
    ¬ Tendsto (fun k : ℕ => (phiSeq n k : ℝ) / (n k : ℝ)) atTop (𝓝 0) := by
  sorry
```

**Variante (D4h; edición respecto al original):**

```lean
theorem erdos_1000.variants.not_tendsto_zero (n : ℕ → ℕ) ⟦(hn0 : 0 < n 0) (hn : StrictMono n)⟧ :
    ¬ Tendsto (fun k : ℕ => (phiSeq n k : ℝ) / (n k : ℝ)) atTop (𝓝 0) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 23. A2∘D1c (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1204:Erdos1204.A_le` (archivo `ErdosProblems/1204`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 4; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> An admissible set of `k` natural numbers inside `[0, m]` gives `A k ≤ m`.

**Lean original:**

```lean
theorem A_le {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S)
    (hm : ∀ a ∈ S, a ≤ m) : A k ≤ m := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem A_le {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S)
    (hm : ∀ a ∈ S, a ≤ m) : ⟦m ≥ A k⟧ := by
  sorry
```

**Variante infiel (A2∘D1c; edición respecto a la base):**

```lean
theorem A_le {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S)
    (hm : ∀ a ∈ S, a ≤ m) : m ⟦>⟧ A k := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 24. A3∘D1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[69]` (archivo `FormalMATH_lite[69]`; FormalMATH-Lite); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Given $f\left(\frac{ y }{ x }\right) = \frac{ \sqrt{x^2+y^2} }{ x }$ and $x > 0$, find $f(x)$.
>  Prove that the answer is: The final answer: $f(x)=\sqrt{1+x^2}$

**Lean original:**

```lean
open Real

theorem u_math_661 {f : ℝ → ℝ}
    (hf : ∀ x y, f (y / x) = sqrt (x ^ 2 + y ^ 2) / x)
    (hx : 0 < x) : f x = sqrt (1 + x ^ 2) := by
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
open Real

theorem u_math_661 {f : ℝ → ℝ}
    (hf : ∀ x y, f (y / x) = sqrt (x ^ 2 + y ^ 2) / x)
    (hx : ⟦x > 0⟧) : f x = sqrt (1 + x ^ 2) := by
```

**Variante infiel (A3∘D1; edición respecto a la base):**

```lean
open Real

theorem u_math_661 {f : ℝ → ℝ}
    (hf : ∀ x y, f (y / x) = sqrt (x ^ 2 + y ^ 2) / x)
    (hx : x ⟦≥⟧ 0) : f x = sqrt (1 + x ^ 2) := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 25. A1∘D8 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1190:Erdos1190.erdos_1190.variants.lt_one` (archivo `ErdosProblems/1190`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 8; respecto a la base fiel: 8; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Erdős [Er80] seems to credit Mirsky and Newman with the result that $\epsilon_m<1$, but gives no
> reference.

**Lean original:**

```lean
theorem erdos_1190.variants.lt_one (m : ℕ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem erdos_1190.variants.lt_one (m : ℕ) (hm : ⟦0 < m⟧) (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  sorry
```

**Variante infiel (A1∘D8; edición respecto a la base):**

```lean
theorem erdos_1190.variants.lt_one (m : ℕ)⟦⟧ (S : Finset ℕ) (a : ℕ → ℤ)
    (hS : ∀ n ∈ S, m < n)
    (hdisj : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' → ¬ ∃ x : ℤ, x ≡ a n [ZMOD n] ∧ x ≡ a n' [ZMOD n']) :
    (∑ n ∈ S, (n : ℝ)⁻¹) < 1 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 26. B3∘D8 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/3161:OeisA3161.conjecture` (archivo `OEIS/3161`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 1; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> "Conjecture: Let $b(n) = a(2n-1)$. Then the supercongruence
> $b(np^k) \equiv b(np^{k-1}) \pmod{p^{3k}}$ holds for positive integers $n$ and $k$
> and all primes $p \ge 5$."
> - Peter Bala, Mar 20 2023.
> 
> Lean formalization by Wentao Li, with AI assistance; see [Li26].

**Lean original:**

```lean
theorem conjecture (n k p : ℕ) (hn : 0 < n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem conjecture (n k p : ℕ) (hn : ⟦1 ≤ n⟧) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry
```

**Variante infiel (B3∘D8; edición respecto a la base):**

```lean
theorem conjecture (n k p : ℕ) (hn : 1 ⟦<⟧ n) (hk : 0 < k) (hp : p.Prime) (hp_ge : 5 ≤ p) :
    (b (n * p ^ k) : ℤ) ≡ (b (n * p ^ (k - 1)) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 27. A3∘D8 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/626:Erdos626.h_of_le_two` (archivo `ErdosProblems/626`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 1; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Every cycle has length at least $3$, so for $m \leq 2$ the girth condition is vacuous and
> $h^{(m)}(n) = n$.

**Lean original:**

```lean
theorem h_of_le_two (m n : ℕ) (hm : m ≤ 2) : h m n = n := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem h_of_le_two (m n : ℕ) (hm : ⟦m < 3⟧) : h m n = n := by
  sorry
```

**Variante infiel (A3∘D8; edición respecto a la base):**

```lean
theorem h_of_le_two (m n : ℕ) (hm : m ⟦≤⟧ 3) : h m n = n := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 28. B2∘D1c (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/882:Erdos882.erdos_882.variants.lower_bound_explicit` (archivo `ErdosProblems/882`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 20; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> The lower bound of [ELRSS99] in quantitative form: for every $n \geq 1$ there is a subset-sum
> antichain $A \subseteq \{1, \ldots, n\}$ with $\lvert A\rvert > \log_2 n - 1$, namely $A_m$
> with $m = \lfloor \log_2 n \rfloor$ (by `erdos_882.variants.lower_bound`, `A_subset_Icc`
> and `card_A`).
> 
> A sorry-free Lean 4 proof of this statement is the theorem `erdos_882` of [Alexeev].
> That formalisation expresses the antichain condition as primitivity of the *set* of nonempty
> subset sums (no element divides another one). For $A \subseteq \{1, \ldots, n\}$ this is
> equivalent to `IsSubsetSumAntichain A`: if two distinct subsets had the same sum, then
> removing their common elements would leave two disjoint […]

**Lean original:**

```lean
theorem erdos_882.variants.lower_bound_explicit (n : ℕ) (hn : 0 < n) :
    Real.logb 2 n - 1 < (maxAntichainCard n : ℝ) := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem erdos_882.variants.lower_bound_explicit (n : ℕ) (hn : 0 < n) :
    ⟦(maxAntichainCard n : ℝ) > Real.logb 2 n - 1⟧ := by
  sorry
```

**Variante infiel (B2∘D1c; edición respecto a la base):**

```lean
theorem erdos_882.variants.lower_bound_explicit (n : ℕ) (hn : 0 < n) :
    (maxAntichainCard n : ℝ) ⟦≥⟧ Real.logb 2 n - 1 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 29. C2∘D8 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/397588:OeisA397588.conjecture_parity` (archivo `OEIS/397588`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> "Conjecture: $a(n)$ is odd iff $n$ is a power of $2$ for $n \ge 1$."
> - Paul D. Hanna, Jul 03 2026.
> 
> Lean formalization by Wentao Li, with AI assistance; see [Li26].

**Lean original:**

```lean
theorem conjecture_parity (n : ℕ) (hn : 1 ≤ n) :
    Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem conjecture_parity (n : ℕ) (hn : ⟦0 < n⟧) :
    Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k := by
  sorry
```

**Variante infiel (C2∘D8; edición respecto a la base):**

```lean
theorem conjecture_parity (n : ℕ) (hn : 0 < n) :
    Odd (a n) ↔ ∃ k : ℕ, n = ⟦3⟧ ^ k := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 30. A2∘D8 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1141:Erdos1141.erdos_1141.variants.mertens_third` (archivo `ErdosProblems/1141`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> **Mertens' third theorem** [Me1874], in the weakened form the linked proof assumes: the product
> over the primes up to $n$ of $1 - 1/p$ is at least $1/(3\log n)$.
> 
> The true asymptotic is $e^{-\gamma}/\log n$, and $e^{-\gamma} > 1/3$, so this bound is weaker than
> the theorem and is what the deduction needs.

**Lean original:**

```lean
theorem erdos_1141.variants.mertens_third (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem erdos_1141.variants.mertens_third (n : ℕ) (hn : ⟦2 < n⟧) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry
```

**Variante infiel (A2∘D8; edición respecto a la base):**

```lean
theorem erdos_1141.variants.mertens_third (n : ℕ) (hn : 2 < n) :
    1 / (3 * Real.log n) ⟦<⟧ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:
