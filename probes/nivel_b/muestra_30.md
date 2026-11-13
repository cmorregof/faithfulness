# Muestra aleatoria de 30 candidatos (Nivel B) — para revisión de Carlos

Generada por `probes/nivel_b/hacer_muestra.py` (semilla 20261104) sobre `candidatos.jsonl` (9025 candidatos; SHA-256 en `resumen_generacion.json`). Estratificada por familia: A (más fuerte) 8, B (más débil) 7, C (otro teorema) 7, D (reescritura fiel) 8; uniforme dentro de cada familia. **Nada está certificado.** La edición va entre ⟦ ⟧ (en el original, lo que se quita o cambia; en la variante, lo que se pone). Se omiten las líneas `import`.

Para cada caso: ¿la etiqueta esperada es correcta respecto al NL? ¿la variante es un enunciado sensato (no un error de tipo disfrazado)? Anotar ✔/✘ y un comentario.

## 1. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:OEIS/2:OeisA2.cursor_lt_prefix_length` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 10; dirección trivial: ambas; correlato en el NL: no; en el emparejamiento provisional: no

**NL:**

> The read cursor used to generate the next run is always inside the generated prefix.

**Lean original:**

```lean
theorem cursor_lt_prefix_length (n : ℕ) : ⟦n + 2 < (wordPrefix n).length⟧ := by
  sorry
```

**Variante:**

```lean
theorem cursor_lt_prefix_length (n : ℕ) : ⟦(wordPrefix n).length > n + 2⟧ := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 2. D6 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/210:Erdos210.le_f_iff` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: ambas; correlato en el NL: no; en el emparejamiento provisional: no

**NL:**

> The infimum is exactly the largest uniform lower bound over all configurations.

**Lean original:**

```lean
theorem le_f_iff {n m : ℕ} (⟦hn⟧ : 3 ≤ n) :
    m ≤ f n ↔ ∀ s : Finset ℝ², s.card = n → ¬ Collinear ℝ (s : Set ℝ²) →
      m ≤ (ordinaryLines s).card := by
  sorry
```

**Variante:**

```lean
theorem le_f_iff {n m : ℕ} (⟦hn₀⟧ : 3 ≤ n) :
    m ≤ f n ↔ ∀ s : Finset ℝ², s.card = n → ¬ Collinear ℝ (s : Set ℝ²) →
      m ≤ (ordinaryLines s).card := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 3. A3 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Other/SuffixPrefixAvoidance:SuffixPrefixAvoidance.suffix_prefix_avoidance_bound` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> $A$ and $B$ are sets of words of length $n$ over alphabet with $q \geq 1$ letters.
> No suffix of a word in $A$ coincides with a prefix of a word in $B$.
> Then $|A| \cdot |B|$ is at most $\frac{q^{2n}}{en}$.
> 
> This problem is from *Maximal sets of strings with no prefix-suffix overlap* and was proved in
> *An isoperimetric inequality for word overlap*.

**Lean original:**

```lean
theorem suffix_prefix_avoidance_bound
    (A B : Finset (Fin n → Fin q))
    (hq : 0 ⟦<⟧ q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n) := by
  sorry
```

**Variante:**

```lean
theorem suffix_prefix_avoidance_bound
    (A B : Finset (Fin n → Fin q))
    (hq : 0 ⟦≤⟧ q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n) := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 4. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[120]` (FormalMATH-Lite); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> The digits in a two-digit positive integer are reversed. The new two-digit integer minus the original integer equals 54. What is the positive difference between the two digits of the original integer?
>  Prove that the answer is: 6

**Lean original:**

```lean
open Nat

theorem omni_theorem_3054 {a b : ℕ} (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (h : (10 * b + a) - (10 * a + b) = ⟦54⟧) : |(a : ℤ) - b| = 6 := by
```

**Variante:**

```lean
open Nat

theorem omni_theorem_3054 {a b : ℕ} (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (h : (10 * b + a) - (10 * a + b) = ⟦55⟧) : |(a : ℤ) - b| = 6 := by
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 5. D6 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:Paper/VoronovskajaTypeFormula:VoronovskajaTypeFormula.bezier_weight_nonneg` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: ambas; correlato en el NL: no; en el emparejamiento provisional: no

**NL:**

> Every Bézier--Bernstein coefficient is nonnegative on the unit interval.

**Lean original:**

```lean
theorem bezier_weight_nonneg {n k : ℕ} {α x : ℝ} (⟦hα⟧ : 0 < α) (hx : x ∈ I) :
    0 ≤ (bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α := by
  sorry
```

**Variante:**

```lean
theorem bezier_weight_nonneg {n k : ℕ} {α x : ℝ} (⟦hα₀⟧ : 0 < α) (hx : x ∈ I) :
    0 ≤ (bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 6. B3 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/357513:OeisA357513.a357513_supercongruence` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> We have  $a(p-1) \equiv 0 \pmod{p^4}$ for all primes $p \ge 3$ except $p=7$.
> 
> proved by AlphaProof

**Lean original:**

```lean
theorem a357513_supercongruence (p : ℕ) (hp : p.Prime) (h_ge3 : p ⟦≥⟧ 3) (h_neq7 : p ≠ 7) :
    (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4] := by
  sorry
```

**Variante:**

```lean
theorem a357513_supercongruence (p : ℕ) (hp : p.Prime) (h_ge3 : p ⟦>⟧ 3) (h_neq7 : p ≠ 7) :
    (a (p - 1) : ℤ) ≡ 0 [ZMOD (p : ℤ) ^ 4] := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 7. A2 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/423:Erdos423.IsHofstadterSeq.le_apply` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> A Hofstadter sequence satisfies `n ≤ a n` for `n ≥ 1`.

**Lean original:**

```lean
theorem IsHofstadterSeq.le_apply {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (n : ℕ)
    (hn : 1 ≤ n) : n ⟦≤⟧ a n := by
  sorry
```

**Variante:**

```lean
theorem IsHofstadterSeq.le_apply {a : ℕ → ℕ} (ha : IsHofstadterSeq a) (n : ℕ)
    (hn : 1 ≤ n) : n ⟦<⟧ a n := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 8. A3 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[56]` (FormalMATH-Lite); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> Does there exist positive integers $n_1, n_2, \dots, n_{2022}$ such that the number
> $$
>   \left( n_1^{2020} + n_2^{2019} \right)\left( n_2^{2020} + n_3^{2019} \right) \cdots \left( n_{2021}^{2020} + n_{2022}^{2019} \right)\left( n_{2022}^{2020} + n_1^{2019} \right)
> $$
> is a power of $11$?
>  Prove that the answer is: \text{No}

**Lean original:**

```lean
theorem omni_theorem_4058 (n : Fin 2022 → ℕ) (hpos : ∀ i, n i ⟦>⟧ 0) :
    ¬∃ k, ∏ i, (n i ^ 2020 + n ((i + 1) % 2022) ^ 2019) = 11 ^ k := by
```

**Variante:**

```lean
theorem omni_theorem_4058 (n : Fin 2022 → ℕ) (hpos : ∀ i, n i ⟦≥⟧ 0) :
    ¬∃ k, ∏ i, (n i ^ 2020 + n ((i + 1) % 2022) ^ 2019) = 11 ^ k := by
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 9. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/24356:OeisA24356.a_2` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> Value of the sequence `a` at 2.

**Lean original:**

```lean
theorem a_2 : a ⟦2⟧ = 1 := by
  sorry
```

**Variante:**

```lean
theorem a_2 : a ⟦3⟧ = 1 := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 10. B3 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1089:Erdos1089.erdos_1089.variants.bounds_and_limit` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> For $n \ge 2$ one has $\binom{d+1}{n-1} + 1 \le g_d(n) \le \binom{d+n-1}{n-1} + 1$ for all
> $d \ge 1$, and $g_d(n) / d^{n-1} \to 1/(n-1)!$ as $d \to \infty$.

**Lean original:**

```lean
theorem erdos_1089.variants.bounds_and_limit (n : ℕ) (hn : 2 ⟦≤⟧ n) :
    (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  sorry
```

**Variante:**

```lean
theorem erdos_1089.variants.bounds_and_limit (n : ℕ) (hn : 2 ⟦<⟧ n) :
    (∀ d, 1 ≤ d → (d + 1).choose (n - 1) + 1 ≤ g d n ∧ g d n ≤ (d + n - 1).choose (n - 1) + 1) ∧
      Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1)) atTop
        (𝓝 ((1 : ℝ) / (n - 1).factorial)) := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 11. A3 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Wikipedia/ReconstructionConjecture:ReconstructionConjecture.edge_reconstruction_conjecture.variants.mueller` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> **Müller (1977): graphs with many edges are edge-reconstructible.**
> 
> If a graph on `n` vertices with `m` edges satisfies `n! < 2 ^ (m - 1)`, then it is determined
> up to isomorphism by its deck of edge-deleted subgraphs.
> 
> *Reference:* [Mu77].

**Lean original:**

```lean
theorem edge_reconstruction_conjecture.variants.mueller {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ⟦<⟧ 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry
```

**Variante:**

```lean
theorem edge_reconstruction_conjecture.variants.mueller {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hE : Nat.factorial (Fintype.card V) ⟦≤⟧ 2 ^ (G.edgeSet.ncard - 1))
    (h : EdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 12. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/91:Erdos91.erdos_91.variants.four` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> For $n=4$ the square or two equilateral triangles sharing an edge give two
> non-similar examples.

**Lean original:**

```lean
theorem erdos_91.variants.four : ¬ UniqueMinimizer ⟦4⟧ := by
  sorry
```

**Variante:**

```lean
theorem erdos_91.variants.four : ¬ UniqueMinimizer ⟦5⟧ := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 13. A3 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/270:Erdos270.erdos_270.variants.every_value` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> Crmarić and Kovač [CrKo25]: for any $\alpha \in (0,\infty)$ there exists a function
> $f:\mathbb{N}\to\mathbb{N}$ such that $f(n)\to \infty$ as $n\to\infty$ and
> $$\sum_{n\geq 1} \frac{1}{(n+1)\cdots (n+f(n))}=\alpha.$$

**Lean original:**

```lean
theorem erdos_270.variants.every_value (α : ℝ) (hα : 0 ⟦<⟧ α) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α := by
  sorry
```

**Variante:**

```lean
theorem erdos_270.variants.every_value (α : ℝ) (hα : 0 ⟦≤⟧ α) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      HasSum (fun n : ℕ => (∏ i ∈ Finset.Icc (n + 2) (n + 1 + f (n + 1)), (i : ℝ))⁻¹) α := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 14. B2 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/504:Erdos504.erdos_504.variants.erdos_szekeres_1960` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> The lower-bound half of `erdos_504` in existential form (Theorem 1 of
> [ErSz60]): any $2^n$ points of the plane contain three points determining an
> angle strictly greater than $\pi(1 - 1/n)$.

**Lean original:**

```lean
theorem erdos_504.variants.erdos_szekeres_1960 {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℂ) (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π ⟦<⟧ EuclideanGeometry.angle p q r := by
  sorry
```

**Variante:**

```lean
theorem erdos_504.variants.erdos_szekeres_1960 {n : ℕ} (hn : 3 ≤ n)
    (S : Finset ℂ) (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π ⟦≤⟧ EuclideanGeometry.angle p q r := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 15. A1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Books/BugeaudDistributionModuloOne/Problem10_61:Bugeaud61.problem_10_61.variants.covering_criterion` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 9; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> The covering criterion, [Ste26, Theorem C(i)], at a quadratic setup: $\alpha > 1$ is a root
> of $X^2 - aX - b$ whose conjugate $\beta = a - \alpha$ is non-zero of modulus less than
> one. If the Route A exponent $A(\alpha)$ formed from $\alpha$ and $\rho = |\beta|$ is
> below $1$, then Problem 10.61 holds at $\alpha$.
> 
> [Ste26] states the criterion for a Pisot number of any degree $d \ge 2$, but proves it only
> in this degree-two case.

**Lean original:**

```lean
theorem problem_10_61.variants.covering_criterion {a b : ℤ} {α : ℝ}
    (hroot : α ^ 2 = a * α + b)⟦ (hα : 1 < α)⟧ (hβ : (a : ℝ) - α ≠ 0)
    (hconj : |(a : ℝ) - α| < 1) (hA : routeAExponent α |(a : ℝ) - α| < 1) :
    ∀ ξ ∈ pisotCantorSet α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1) := by
  sorry
```

**Variante:**

```lean
theorem problem_10_61.variants.covering_criterion {a b : ℤ} {α : ℝ}
    (hroot : α ^ 2 = a * α + b)⟦⟧ (hβ : (a : ℝ) - α ≠ 0)
    (hconj : |(a : ℝ) - α| < 1) (hA : routeAExponent α |(a : ℝ) - α| < 1) :
    ∀ ξ ∈ pisotCantorSet α, ¬ IsEquidistributedModuloOne fun n : ℕ => ξ * α ^ (n + 1) := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 16. A3 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/237271:OeisA237271.conjecture_1` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> Conjecture 1 / Theorem: "a(n) is the number of odd divisors of n except the 'e' odd
> divisors described in A005279." - _Omar E. Pol_, Dec 21 2024.
> "The conjecture 1 is true. For a proof see A379288." - _Hartmut F. W. Hoft_, Jan 21 2025.
> Equivalently, $a(n) = \text{A001227}(n) - \text{A239657}(n)$. - _Omar E. Pol_, Mar 23 2014

**Lean original:**

```lean
theorem conjecture_1 (n : ℕ) (hn : 0 ⟦<⟧ n) :
    a n = A001227 n - A239657 n := by
  sorry
```

**Variante:**

```lean
theorem conjecture_1 (n : ℕ) (hn : 0 ⟦≤⟧ n) :
    a n = A001227 n - A239657 n := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 17. B2 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/964:Erdos964.tauRatio_pos` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> For $n \geq 1$ the ratio $\tau(n+1)/\tau(n)$ is positive.

**Lean original:**

```lean
theorem tauRatio_pos {n : ℕ} (hn : 0 < n) : 0 ⟦<⟧ tauRatio n := by
  sorry
```

**Variante:**

```lean
theorem tauRatio_pos {n : ℕ} (hn : 0 < n) : 0 ⟦≤⟧ tauRatio n := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 18. A2 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/819:Erdos819.card_add_self_le` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: variante ⇒ original; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> Every sum $a + b$ with $a, b \in A$ comes from an unordered pair $\{a, b\}$, so
> $\lvert A + A\rvert \leq \binom{\lvert A\rvert + 1}{2}$.

**Lean original:**

```lean
theorem card_add_self_le (A : Finset ℕ) : #(A + A) ⟦≤⟧ (#A + 1).choose 2 := by
  sorry
```

**Variante:**

```lean
theorem card_add_self_le (A : Finset ℕ) : #(A + A) ⟦<⟧ (#A + 1).choose 2 := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 19. D8 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/504:Erdos504.erdos_504.variants.erdos_szekeres_1960` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 2; dirección trivial: ambas; correlato en el NL: sí; en el emparejamiento provisional: sí

**NL:**

> The lower-bound half of `erdos_504` in existential form (Theorem 1 of
> [ErSz60]): any $2^n$ points of the plane contain three points determining an
> angle strictly greater than $\pi(1 - 1/n)$.

**Lean original:**

```lean
theorem erdos_504.variants.erdos_szekeres_1960 {n : ℕ} (hn : ⟦3 ≤ n⟧)
    (S : Finset ℂ) (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  sorry
```

**Variante:**

```lean
theorem erdos_504.variants.erdos_szekeres_1960 {n : ℕ} (hn : ⟦2 < n⟧)
    (S : Finset ℂ) (hcard : S.card = 2 ^ n) :
    ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ r ≠ q ∧
      (1 - 1 / (n : ℝ)) * π < EuclideanGeometry.angle p q r := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 20. B3 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:WrittenOnTheWallII/GraphConjecture217:WrittenOnTheWallII.GraphConjecture217.conjecture217` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> WOWII [Conjecture 217](http://cms.uhd.edu/faculty/delavinae/research/wowII/all.html#conj217):
> 
> If $G$ is a finite simple connected graph on $n > 1$ vertices and
> $L_s(G) \le 4 \cdot \chi_{\mathrm{residue}=2}(G) + 2$,
> then $G$ has a Hamiltonian path. Here $L_s(G)$ is the maximum number of
> leaves over all spanning trees and $\chi_{\mathrm{residue}=2}(G)$ is the indicator
> of $\mathrm{residue}(G) = 2$.

**Lean original:**

```lean
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ⟦≤⟧ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry
```

**Variante:**

```lean
theorem conjecture217 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected)
    (hL : Ls G ⟦<⟧ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 21. D3 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/486:Erdos486.erdos_486` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 2; dirección trivial: ambas; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> Let $A \subseteq \mathbb{N}$, and for each $n \in A$ choose some
> $X_n \subseteq \mathbb{Z}/n\mathbb{Z}$. Let
> $B = \{m \in \mathbb{N} : m \not\in X_n \pmod{n} \text{ for all } n \in A \text{ with } m > n\}$.
> Must $B$ have a logarithmic density?
> 
> The set $A$ is encoded by taking $X_n = \emptyset$ for $n \notin A$. Only positive moduli
> $n$ are considered, since $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$ would allow $B$ to be an
> arbitrary set.
> 
> The answer is no: Wang [Wa26] (with GPT-5.6) constructed a congruence system whose survivor set
> $B$ has lower logarithmic density at most $177/200$ and upper logarithmic density at least
> $49/50$. The first linked formal proof establishes this for the real-cuto […]

**Lean original:**

```lean
theorem erdos_486 :
    ¬ ∀ ⟦X⟧ : (n : ℕ) → Set (ZMod n),
      ∃ d, {m : ℕ | ∀ n, 0 < n → n < m → (m : ZMod n) ∉ ⟦X⟧ n}.HasLogDensity d := by
  sorry
```

**Variante:**

```lean
theorem erdos_486 :
    ¬ ∀ ⟦X₁⟧ : (n : ℕ) → Set (ZMod n),
      ∃ d, {m : ℕ | ∀ n, 0 < n → n < m → (m : ZMod n) ∉ ⟦X₁⟧ n}.HasLogDensity d := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 22. B3 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/835:Erdos835.chromaticNumber_johnson_2k_k_lower_bound_odd` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 1; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> It is also known that for $3 \leq k \leq 203$ odd, the chromatic number of $J(2k, k)$ is
> greater than $k+1$, see [Johnson graphs](https://aeb.win.tue.nl/graphs/Johnson.html).

**Lean original:**

```lean
theorem chromaticNumber_johnson_2k_k_lower_bound_odd (hk : 3 ⟦≤⟧ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  sorry
```

**Variante:**

```lean
theorem chromaticNumber_johnson_2k_k_lower_bound_odd (hk : 3 ⟦<⟧ k) (hk' : k ≤ 300) (hk_odd : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 23. D3 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:Arxiv/2504.17644/Margulis:Margulis.huang_shi_theorem_1_2` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 3; dirección trivial: ambas; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> **Huang–Shi, Theorem 1.2**
> 
> Let `F` be a finite field of characteristic `p ∈ {3, 5, 7, 11}`, and set
> `K = F((t⁻¹))`, `A = F[t]`. Here `K` is modelled by the Laurent series field `F⸨X⸩` with
> `X = t⁻¹`, so that `A` is embedded via `t ↦ X⁻¹`. Let
> 
> * `D` be the diagonal subgroup of `SL₄(K)`,
> * `Γ = SL₄(A)` the lattice subgroup embedded into `SL₄(K)` via the natural inclusion `A →+* K`.
> 
> Then there exists `z : SL₄(K)/Γ` such that the `D`-orbit of `z` has compact
> closure but is not closed.

**Lean original:**

```lean
theorem huang_shi_theorem_1_2
    (hchar : ringChar F ∈ ({3, 5, 7, 11} : Finset ℕ)) :
    ∃ ⟦z⟧ : SL(4, F⸨X⸩) ⧸ (  Matrix.SpecialLinearGroup.map
    (polyToLaurent F)).range,
      IsCompact (closure (MulAction.orbit (diagonalSubgroup (Fin 4) (F⸨X⸩)) ⟦z⟧)) ∧
      ¬ IsClosed (MulAction.orbit (diagonalSubgroup (Fin 4) (F⸨X⸩)) ⟦z⟧) := by
  sorry
```

**Variante:**

```lean
theorem huang_shi_theorem_1_2
    (hchar : ringChar F ∈ ({3, 5, 7, 11} : Finset ℕ)) :
    ∃ ⟦z₁⟧ : SL(4, F⸨X⸩) ⧸ (  Matrix.SpecialLinearGroup.map
    (polyToLaurent F)).range,
      IsCompact (closure (MulAction.orbit (diagonalSubgroup (Fin 4) (F⸨X⸩)) ⟦z₁⟧)) ∧
      ¬ IsClosed (MulAction.orbit (diagonalSubgroup (Fin 4) (F⸨X⸩)) ⟦z₁⟧) := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 24. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:Arxiv/2606.03696/BondyLongestCycles:Arxiv.2606.03696.bondy_conjecture.variants.two` (formal_conjectures); zona: hipotesis; tokens editados (Qwen3-4B): 8; dirección trivial: ambas; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> The case $k = 2$ is the theorem of Nash-Williams.

**Lean original:**

```lean
theorem bondy_conjecture.variants.two {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsKConnected G 2) (hd : ⟦((Fintype.card V : ℝ) + 2) / 3 ≤ G.minDegree⟧)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference)
    (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v) (hP : P.IsPath) :
    P.support.length + 1 ≤ 2 := by
  sorry
```

**Variante:**

```lean
theorem bondy_conjecture.variants.two {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : IsKConnected G 2) (hd : ⟦G.minDegree ≥ ((Fintype.card V : ℝ) + 2) / 3⟧)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference)
    (u v : offWalk C) (P : (G.induce (offWalk C)).Walk u v) (hP : P.IsPath) :
    P.support.length + 1 ≤ 2 := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 25. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:WrittenOnTheWallII/Test:WrittenOnTheWallII.Test.petersen_girth` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> Star5: Star graph with center 0 and 5 leaves. -/
> abbrev Star5 : SimpleGraph (Fin 1 ⊕ Fin 5) := completeBipartiteGraph (Fin 1) (Fin 5)
> instance : DecidableRel Star5.Adj := by unfold Star5 completeBipartiteGraph; infer_instance
> 
> /-  ### House Graph Tests -/
> 
> /-  ### K4 Tests -/
> 
> /-  ### Petersen Graph Tests

**Lean original:**

```lean
theorem petersen_girth : PetersenGraph.girth = ⟦5⟧ := by
  sorry
```

**Variante:**

```lean
theorem petersen_girth : PetersenGraph.girth = ⟦6⟧ := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 26. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[332]` (FormalMATH-Lite); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> The expression $(5 \times 5)+(5 \times 5)+(5 \times 5)+(5 \times 5)+(5 \times 5)$ is equal to what?
>  Prove that the answer is: 125

**Lean original:**

```lean
theorem omni_theorem_3438 : (⟦5⟧ * 5) + (5 * 5) + (5 * 5) + (5 * 5) + (5 * 5) = 125 := by
```

**Variante:**

```lean
theorem omni_theorem_3438 : (⟦6⟧ * 5) + (5 * 5) + (5 * 5) + (5 * 5) + (5 * 5) = 125 := by
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 27. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/34694:OeisA34694.a_5` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> Value of the sequence `a` at 5.

**Lean original:**

```lean
theorem a_5 : a ⟦5⟧ = 11 := by
  sorry
```

**Variante:**

```lean
theorem a_5 : a ⟦6⟧ = 11 := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 28. B1 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[13]` (FormalMATH-Lite); zona: hipotesis; tokens editados (Qwen3-4B): 9; dirección trivial: original ⇒ variante; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> If \(n\equiv4(\bmod 9)\), prove that the Diophantine equation
> \[x^{3}+y^{3}+z^{3} = n.\tag{1}\]
> has no integer solutions \((x,y,z)\).

**Lean original:**

```lean
open Real
open scoped BigOperators

theorem algebra_45698 (n : ℤ) (h : n ≡ 4 [ZMOD 9])⟦⟧ :
  ¬∃ x y z : ℤ, x^3 + y^3 + z^3 = n := by
```

**Variante:**

```lean
open Real
open scoped BigOperators

theorem algebra_45698 (n : ℤ) (h : n ≡ 4 [ZMOD 9])⟦ (hn_pos : 0 < n)⟧ :
  ¬∃ x y z : ℤ, x^3 + y^3 + z^3 = n := by
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 29. C2 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/118:Erdos118.erdos_118` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 1; dirección trivial: ninguna; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> **Erdős Problem 118** (problem of Erdős and Hajnal). Let $\alpha$ be such that
> $\alpha \to (\alpha, 3)^2$. For every $n \ge 3$, must $\alpha \to (\alpha, n)^2$?
> 
> The original question is asked for cardinals, ordinals, and order types; we state the
> ordinal version, which is the standard reading: ordinals $\alpha$ with
> $\alpha \to (\alpha, 3)^2$ are called *partition ordinals*.
> 
> The answer is **no**, shown independently by Schipperus [Sc99, Sc10] and Darby [Da99].
> Larson [La00] gave the concrete counterexample $\alpha = \omega^{\omega^2}$, for which
> $\alpha \to (\alpha, 3)^2$ holds yet $\alpha \not\to (\alpha, 5)^2$. See Chapter 2.9 of
> [HST10] for further background.

**Lean original:**

```lean
theorem erdos_118 :
    ¬ ∀ α : Ordinal.{0}, OrdinalRamsey α α ⟦3⟧ →
      ∀ n : ℕ, 3 ≤ n → OrdinalRamsey α α n := by
  sorry
```

**Variante:**

```lean
theorem erdos_118 :
    ¬ ∀ α : Ordinal.{0}, OrdinalRamsey α α ⟦4⟧ →
      ∀ n : ℕ, 3 ≤ n → OrdinalRamsey α α n := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## 30. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/30:Erdos30.erdos_30.variants.lindstrom_weak` (formal_conjectures); zona: conclusion; tokens editados (Qwen3-4B): 6; dirección trivial: ambas; correlato en el NL: sí; en el emparejamiento provisional: no

**NL:**

> A weak form of Lindström's bound [Li69], following from
> `erdos_30.variants.elementary_difference_count`: a Sidon set $A \subseteq \{0, \dots, N\}$
> has $|A| \le \lfloor \sqrt{2N} \rfloor + 1$.

**Lean original:**

```lean
theorem erdos_30.variants.lindstrom_weak (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    ⟦A.card ≤ Nat.sqrt (2 * N) + 1⟧ := by
  sorry
```

**Variante:**

```lean
theorem erdos_30.variants.lindstrom_weak (A : Finset ℕ) (N : ℕ)
    (hS : IsSidon (A : Set ℕ)) (hA : A ⊆ Finset.range (N + 1)) :
    ⟦Nat.sqrt (2 * N) + 1 ≥ A.card⟧ := by
  sorry
```

Revisión: ☐ etiqueta correcta  ☐ variante sensata — comentario:

## Cambios del revisor (Fable, 2026-11-04)

Revisé los 30 casos uno por uno (sin Lean). No cambié ninguna etiqueta impresa; anoto aquí los casos cuya etiqueta esperada está mal descrita o no se puede juzgar, y lo que debe cambiar en la muestra.

- **Caso 25 (C2, `petersen_girth`): el «NL» no es un enunciado.** Es el docstring de `Star5` seguido de código Lean (`abbrev Star5 …`, `instance …`) y comentarios de sección; error de extracción de `doc_nl` (corregido en `generar.py`). Respecto a ese texto no hay etiqueta posible, ni para el original ni para la variante. Hay 25 orígenes así en el lote (26 candidatos; 1 origen con par provisional).
- **Caso 22 (B3, `chromaticNumber_johnson_2k_k_lower_bound_odd`): el original ya es infiel al NL.** El docstring dice `3 ≤ k ≤ 203` y el Lean `k ≤ 300` (comprobado en `corpus_v2.jsonl`). La variante `3 < k` sigue siendo inadecuada, pero la premisa del diseño (original adecuado) falla, y la D que se emparejara con este origen recibiría «adecuada» sin serlo respecto al NL.
- **Caso 16 (A3, `OeisA237271.conjecture_1`): etiqueta dudosa.** El NL («a(n) is the number of odd divisors of n …») no restringe `n`; el correlato pasó por la letra `n`. Que `0 < n` → `0 ≤ n` sea «inadecuada» depende de la convención n ≥ 1 de la OEIS, no del texto. En ℕ, además, `0 ≤ n` es vacua (equivale a A1).
- **Casos 3 y 8 (A3 en ℕ):** `0 ≤ q` y `n i ≥ 0` son vacuos en ℕ; la etiqueta inadecuada es correcta (el NL dice `q ≥ 1` y «positive integers»), pero la certificación de nivel 2 no encontrará testigo (variables `A B : Finset …`, `n : Fin 2022 → ℕ`) y quedarán «sin_decidir». En el caso 3, `q` y `n` son variables del contexto, no binders.
- **Casos 19 y 24 (D8, D1):** la hipótesis editada (`3 ≤ n`; la cota de grado mínimo) no aparece en el NL, que es una nota («The case k = 2 is the theorem of Nash-Williams»). La etiqueta «adecuada» respecto al original es correcta; respecto al NL no se puede juzgar.
- **Caso 4 (C2, `= 54` → `= 55`):** etiqueta correcta; la variante tiene hipótesis insatisfacible (la diferencia de dígitos invertidos es múltiplo de 9) y es verdadera por vacuidad. La rejilla de testigos no alcanza (a, b) = (1, 7) (ver `reglas_generador.md`, cambios del revisor, punto 8).
- Los demás 23 casos: etiqueta esperada correcta respecto al NL y variante sensata, a mi juicio. En los casos 7, 11, 13, 17, 18 y 26 la variante es además falsa (o verdadera por vacuidad en 4 y 28): irrelevante para la fidelidad, pertinente para el control §5.
- **La muestra no sirve para aprobar las reglas que entran en los pares.** Está estratificada por familia y es uniforme sobre todos los candidatos, así que 5 de los 8 casos D son D3/D6 (excluidas de los pares) y no hay ningún A1 salvo el 15, ni B4, C1, C3, D4h, D4c, D5 ni D1c, y un solo D8 (la fiel más usada en los pares, 289 de 730). Propongo una segunda muestra de ~30 tomada **solo entre candidatos en el emparejamiento provisional**, estratificada por regla (1–3 por regla), con dos preguntas por caso: «¿el original es adecuado al NL?» y «¿la etiqueta de la variante es correcta respecto al NL?».
