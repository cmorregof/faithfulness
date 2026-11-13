# Muestra v3 (Nivel B) — para revisión de Carlos

Generada por `probes/nivel_b/hacer_muestra_v3.py` (semilla 20261104) sobre `candidatos_v3.jsonl` (9472 candidatos; SHA-256 `7dd3b05246d20a1548ccc1d89371b191e58cc15d4175e99e5eb53edbc37ea413`), **solo entre los 1780 candidatos del emparejamiento provisional** (890 pares), estratificada por regla (27 reglas; 30 casos). **Nada está certificado.** La edición va entre ⟦ ⟧. Se omiten las líneas `import`. `muestra_30.md` (v1) y `muestra_30_v2.md` quedan intactas como histórico. Lote v3: v2 + los 7 cambios de `revision_muestra_v2_fable.md` §4 (nombres de teorema neutros: `theorem T`).

Para cada caso, tres preguntas: **(P0) ¿el Lean ORIGINAL es fiel al NL?** (premisa del diseño; si no, el par no vale); (P1) ¿la etiqueta esperada de la variante es correcta respecto al NL?; (P2) ¿la variante es un enunciado sensato (no un error de tipo disfrazado)? Anotar ✔/✘ y un comentario.

## 1. B2∘D8 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/835:Erdos835.johnson_chromaticNumber_odd` (archivo `ErdosProblems/835`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> It can be seen that the chromatic number of $J(2k,k)$ is $>k+1$ for all odd $k>2$.

**Lean original:**

```lean
theorem T (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T (k : ℕ) (hk : ⟦3 ≤ k⟧) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  sorry
```

**Variante infiel (B2∘D8; edición respecto a la base):**

```lean
theorem T (k : ℕ) (hk : 3 ≤ k) (h : Odd k) :
    k + 1 ⟦≤⟧ J(2 * k, k).chromaticNumber := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 2. D4c (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `FormalMATH_lite[217]` (archivo `FormalMATH_lite[217]`; FormalMATH-Lite); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 12; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> Given the equation
> $$
> (ax + 1)^2=a^2(1 - x^2),
> $$
> where \(a\gt1\). Prove that the positive root of the equation is less than \(1\) and the negative root is greater than \(- 1\).

**Lean original:**

```lean
theorem T (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ)
    (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2))
    (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    x₁ < 1 ∧ x₂ > -1 := by
```

**Variante (D4c; edición respecto al original):**

```lean
theorem T (a : ℝ) (ha : a > 1) (x₁ x₂ : ℝ)
    (h₁ : (a * x₁ + 1) ^ 2 = a ^ 2 * (1 - x₁ ^ 2)) (h₂ : (a * x₂ + 1) ^ 2 = a ^ 2 * (1 - x₂ ^ 2))
    (hx₁ : x₁ > 0) (hx₂ : x₂ < 0) :
    ⟦x₂ > -1 ∧ x₁ < 1⟧ := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 3. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/504:Erdos504.erdos_504.variants.sendov` (archivo `ErdosProblems/504`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> **Sendov (1995).** The complete determination: for $n \ge 3$,
> $\alpha_N = \pi(1 - 1/n)$ whenever $2^{n-1} + 2^{n-3} < N \le 2^n$, and
> $\alpha_N = \pi\left(1 - \frac{2}{2n - 1}\right)$ whenever
> $2^{n-1} < N \le 2^{n-1} + 2^{n-3}$.
> 
> This is the statement of [Se95] (as given in Zbl 0853.52009) with $n$ shifted by one.
> For $n = 3$ the second branch gives $\alpha_5 = 3\pi/5$, the value computed in [ErSz60],
> and $\alpha_N$ is nondecreasing in $N$ across the two branches.
> The problem page [erdosproblems.com/504](https://www.erdosproblems.com/504) prints the
> second branch as $\pi(1 - \frac{1}{2n-1})$, which would give $\alpha_5 = 4\pi/5 > \alpha_6$;
> that appears to be a typo.

**Lean original:**

```lean
theorem T {n N : ℕ} (hn : 3 ≤ n)
    (h1 : 2 ^ (n - 1) < N) (h2 : N ≤ 2 ^ n) :
    minimaxAngle N =
      if 2 ^ (n - 1) + 2 ^ (n - 3) < N then (1 - 1 / (n : ℝ)) * π
      else (1 - 2 / (2 * (n : ℝ) - 1)) * π := by
  sorry
```

**Variante (D1; edición respecto al original):**

```lean
theorem T {n N : ℕ} (hn : ⟦n ≥ 3⟧)
    (h1 : 2 ^ (n - 1) < N) (h2 : N ≤ 2 ^ n) :
    minimaxAngle N =
      if 2 ^ (n - 1) + 2 ^ (n - 3) < N then (1 - 1 / (n : ℝ)) * π
      else (1 - 2 / (2 * (n : ℝ) - 1)) * π := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 4. B2∘D1c (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/382:Erdos382.lt_two_mul_of_largestPrimeRepeated` (archivo `ErdosProblems/382`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 4; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> If the condition holds, then $v < 2u$.
> 
> Otherwise $2u \leq v$, and by Bertrand's postulate there is a prime $q$ with $v/2 < q \leq v$, so
> $u \leq q \leq v$. The largest prime $p$ of the product satisfies $p \geq q > v/2$. Hence $p$
> divides exactly one factor $m \in [u, v]$, namely $m = p$, and $p$ appears with exponent $1$.

**Lean original:**

```lean
theorem T {u v : ℕ} (h : LargestPrimeRepeated u v) :
    v < 2 * u := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem T {u v : ℕ} (h : LargestPrimeRepeated u v) :
    ⟦2 * u > v⟧ := by
  sorry
```

**Variante infiel (B2∘D1c; edición respecto a la base):**

```lean
theorem T {u v : ℕ} (h : LargestPrimeRepeated u v) :
    2 * u ⟦≥⟧ v := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 5. B3∘D1 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[10]` (archivo `FormalMATH_lite[10]`; FormalMATH-Lite); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> Proof: $\sum_{k = 0}^{\left[\frac{n - 1}{2}\right]}(-1)^k\mathrm{C}_{n + 1}^k\mathrm{C}_{2n - 2k - 1}^n=\frac{1}{2}n(n + 1)\ (n\geqslant1)$

**Lean original:**

```lean
open Nat

theorem T {n : ℕ} (hn : 1 ≤ n) :
    ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, (-1 : ℤ)^k * Nat.choose (n + 1) k * Nat.choose (2 * n - 2 * k - 1) n =
    (n * (n + 1)) / 2 := by
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
open Nat

theorem T {n : ℕ} (hn : ⟦n ≥ 1⟧) :
    ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, (-1 : ℤ)^k * Nat.choose (n + 1) k * Nat.choose (2 * n - 2 * k - 1) n =
    (n * (n + 1)) / 2 := by
```

**Variante infiel (B3∘D1; edición respecto a la base):**

```lean
open Nat

theorem T {n : ℕ} (hn : n ⟦>⟧ 1) :
    ∑ k in Finset.Icc 0 ⌊(n - 1) / 2⌋₊, (-1 : ℤ)^k * Nat.choose (n + 1) k * Nat.choose (2 * n - 2 * k - 1) n =
    (n * (n + 1)) / 2 := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 6. A1∘D8 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/423:Erdos423.IsHofstadterSeq.lt_iff_lt` (archivo `ErdosProblems/423`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 11; respecto a la base fiel: 9; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> For indices `≥ 1`, a Hofstadter sequence preserves and reflects `<`.

**Lean original:**

```lean
theorem T {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j) :
    a i < a j ↔ i < j := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ}
    (hi : ⟦0 < i⟧) (hj : 1 ≤ j) :
    a i < a j ↔ i < j := by
  sorry
```

**Variante infiel (A1∘D8; edición respecto a la base):**

```lean
theorem T {a : ℕ → ℕ} (ha : IsHofstadterSeq a) {i j : ℕ}
    (hi : 0 < i)⟦⟧ :
    a i < a j ↔ i < j := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 7. D8 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/644:Erdos644.erdos_644.variants.elementary_upper_bound` (archivo `ErdosProblems/644`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 2; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> For $r \geq 3$, the transversal bound satisfies $f(k,r) \leq 2k$.

**Lean original:**

```lean
theorem T (k r : ℕ) (hr : 3 ≤ r) :
    Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞) := by
  sorry
```

**Variante (D8; edición respecto al original):**

```lean
theorem T (k r : ℕ) (hr : ⟦2 < r⟧) :
    Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 8. C3∘D1 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Paper/CourtadeKumar:CourtadeKumar.courtade_kumar` (archivo `Paper/CourtadeKumar`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 5; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> **The Courtade–Kumar conjecture.** For every $n$, every Boolean function $f$ on
> $\{0,1\}^n$ and every crossover probability $p \in [0, 1]$, $I(f(X); Y) \le 1 - h(p)$.

**Lean original:**

```lean
theorem T (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    mutualInfo f p ≤ 1 - binEntropyBits p := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem T (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : ⟦p ≥ 0⟧) (hp₁ : p ≤ 1) :
    mutualInfo f p ≤ 1 - binEntropyBits p := by
  sorry
```

**Variante infiel (C3∘D1; edición respecto a la base):**

```lean
theorem T (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1) :
    mutualInfo f p ⟦≥⟧ 1 - binEntropyBits p := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 9. A2∘D1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Arxiv/1609.08688/sIncreasingrTuples:Arxiv.1609.08688.maximalLength_pow_eventually` (archivo `Arxiv/1609.08688/sIncreasingrTuples`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 5; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Moreover, for every $\beta < \alpha$ and all sufficiently large $m$ we have
> $F(m) \geq m^{\beta}$.

**Lean original:**

```lean
theorem T {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem T {n : ℕ} {e : ℝ} (hn : ⟦n > 1⟧) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  sorry
```

**Variante infiel (A2∘D1; edición respecto a la base):**

```lean
theorem T {n : ℕ} {e : ℝ} (hn : n > 1) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ⟦<⟧ F m := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 10. B3∘D1c (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/557:Erdos557.erdos_557.variants.tight` (archivo `ErdosProblems/557`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 19; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> The best-possible bound $R_k(T) \leq k(n-2)+2$ for every $k$ and every tree $T$ on $n \geq 2$
> vertices, attained by stars. It follows from the sharp form of the Erdős–Sós theorem (a graph on
> $m$ vertices with more than $(n-2)m/2$ edges contains every tree on $n$ vertices) by the
> pigeonhole principle.

**Lean original:**

```lean
theorem T (k n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : multicolourGraphRamsey k T ≤ k * (n - 2) + 2 := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem T (k n : ℕ) (hn : 2 ≤ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : ⟦k * (n - 2) + 2 ≥ multicolourGraphRamsey k T⟧ := by
  sorry
```

**Variante infiel (B3∘D1c; edición respecto a la base):**

```lean
theorem T (k n : ℕ) (hn : 2 ⟦<⟧ n) (T : SimpleGraph (Fin n))
    (hT : T.IsTree) : k * (n - 2) + 2 ≥ multicolourGraphRamsey k T := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 11. A2∘D8 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/1141:Erdos1141.erdos_1141.variants.mertens_third` (archivo `ErdosProblems/1141`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> **Mertens' third theorem** [Me1874], in the weakened form the linked proof assumes: the product
> over the primes up to $n$ of $1 - 1/p$ is at least $1/(3\log n)$.
> 
> The true asymptotic is $e^{-\gamma}/\log n$, and $e^{-\gamma} > 1/3$, so this bound is weaker than
> the theorem and is what the deduction needs.

**Lean original:**

```lean
theorem T (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T (n : ℕ) (hn : ⟦2 < n⟧) :
    1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry
```

**Variante infiel (A2∘D8; edición respecto a la base):**

```lean
theorem T (n : ℕ) (hn : 2 < n) :
    1 / (3 * Real.log n) ⟦<⟧ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 12. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:Wikipedia/Falconer:Falconer.falconer_conjecture_two` (archivo `Wikipedia/Falconer`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 6; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> Falconer's distance set conjecture, $d = 2$ case.
> 
> This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
> proof.

**Lean original:**

```lean
theorem T (E : Set <| ℝ²) (hc : IsCompact E) (hd : 2 < 2 * dimH E ) :
    0 < volume (image2 dist E E) := by
  sorry
```

**Variante (D1; edición respecto al original):**

```lean
theorem T (E : Set <| ℝ²) (hc : IsCompact E) (hd : ⟦2 * dimH E > 2⟧ ) :
    0 < volume (image2 dist E E) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 13. D4h (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/1212:Erdos1212.anchor_coprime_of_short_leg` (archivo `ErdosProblems/1212`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 16; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> Roughness criterion (sufficiency for the anchor conditions): if $a < s$ for all $s$ in
> the leg and the leg stays below $a + P^-(a)$, then $a$ is coprime to the whole leg. Stated
> via divisibility: no prime factor of $a$ divides any $s$ with $a < s < a + p$ for all
> prime factors $p$ of $a$.

**Lean original:**

```lean
theorem T {a s : ℕ} (hs : a < s)
    (h : ∀ p, p.Prime → p ∣ a → s < a + p) : Nat.gcd a s = 1 := by
  sorry
```

**Variante (D4h; edición respecto al original):**

```lean
theorem T {a s : ℕ} ⟦(h : ∀ p, p.Prime → p ∣ a → s < a + p)
    (hs : a < s)⟧ : Nat.gcd a s = 1 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 14. B2∘D1 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/401006:OeisA401006.lt_a_of_not_prime` (archivo `OEIS/401006`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 5; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> Applying $a$ to a composite integer above one strictly increases its value.

**Lean original:**

```lean
theorem T {n : ℕ} (hn : 1 < n) (hprime : ¬n.Prime) : n < a n := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem T {n : ℕ} (hn : ⟦n > 1⟧) (hprime : ¬n.Prime) : n < a n := by
  sorry
```

**Variante infiel (B2∘D1; edición respecto a la base):**

```lean
theorem T {n : ℕ} (hn : n > 1) (hprime : ¬n.Prime) : n ⟦≤⟧ a n := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 15. A3∘D8 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Wikipedia/EllipticCurveRank:EllipticCurveRank.RatEllipticCurve.goldfeld_conjecture.variants.two_le` (archivo `Wikipedia/EllipticCurveRank`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 1; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> **Goldfeld's conjecture** ([Goldfeld1979], Conjecture B), in the form stated in the
> introduction of [Smith2025], in the case $2 \leq r$: a density $0$ of the quadratic twists $E^d$
> of an elliptic curve $E$ over $\mathbb{Q}$ have rank $r$.
> 
> For the Mordell–Weil rank used here this is an unconditional theorem: by Theorem 1.1 of
> [Smith2025], $100\%$ of the twists $E^d$ have $2^\infty$-Selmer corank $0$ or $1$, and the
> Mordell–Weil rank is at most the $2^\infty$-Selmer corank (equation (1.1) there), so the twists
> of rank at least $2$ have density $0$. The corresponding statement for the analytic rank is
> open.

**Lean original:**

```lean
theorem T (E : RatEllipticCurve) (r : ℕ) (hr : 2 ≤ r) :
    atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0) := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T (E : RatEllipticCurve) (r : ℕ) (hr : ⟦1 < r⟧) :
    atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0) := by
  sorry
```

**Variante infiel (A3∘D8; edición respecto a la base):**

```lean
theorem T (E : RatEllipticCurve) (r : ℕ) (hr : 1 ⟦≤⟧ r) :
    atTop.Tendsto
      (fun H ↦ ({d ∈ twistIndexLE H | E.twistRank d = r}.ncard / (twistIndexLE H).ncard : ℝ))
      (𝓝 0) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 16. C3∘D8 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Arxiv/1609.08688/sIncreasingrTuples:Arxiv.1609.08688.maximalLength_pow_eventually` (archivo `Arxiv/1609.08688/sIncreasingrTuples`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> Moreover, for every $\beta < \alpha$ and all sufficiently large $m$ we have
> $F(m) \geq m^{\beta}$.

**Lean original:**

```lean
theorem T {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T {n : ℕ} {e : ℝ} (hn : ⟦2 ≤ n⟧) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  sorry
```

**Variante infiel (C3∘D8; edición respecto a la base):**

```lean
theorem T {n : ℕ} {e : ℝ} (hn : 2 ≤ n) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ⟦≥⟧ F m := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 17. D1 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:ErdosProblems/1086:Erdos1086.triangleAreaCount_le_g` (archivo `ErdosProblems/1086`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; dirección trivial: ambas; correlato en el NL: no

**NL:**

> A set of points has at most `g n` triangles of any given positive area.

**Lean original:**

```lean
theorem T (P : Finset ℝ²) {a : ℝ} (ha : 0 < a) :
    triangleAreaCount P a ≤ g P.card := by
  sorry
```

**Variante (D1; edición respecto al original):**

```lean
theorem T (P : Finset ℝ²) {a : ℝ} (ha : ⟦a > 0⟧) :
    triangleAreaCount P a ≤ g P.card := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 18. A1∘D4h (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[342]` (archivo `FormalMATH_lite[342]`; FormalMATH-Lite); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 8; respecto a la base fiel: 8; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Suppose that $x$ and $y$ are positive numbers with $xy=\frac{1}{9}$, $x(y+1)=\frac{7}{9}$, and $y(x+1)=\frac{5}{18}$. What is the value of $(x+1)(y+1)$?
>  Prove that the answer is: \frac{35}{18}

**Lean original:**

```lean
theorem T {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1 / 9) (hxy1 : x * (y + 1) = 7 / 9) (hxy2 : y * (x + 1) = 5 / 18) :
    (x + 1) * (y + 1) = 35 / 18 := by
```

**Variante fiel (base D4h, la otra mitad del par; edición respecto al original):**

```lean
theorem T {x y : ℝ} ⟦(hy : 0 < y) (hx : 0 < x)⟧
    (hxy : x * y = 1 / 9) (hxy1 : x * (y + 1) = 7 / 9) (hxy2 : y * (x + 1) = 5 / 18) :
    (x + 1) * (y + 1) = 35 / 18 := by
```

**Variante infiel (A1∘D4h; edición respecto a la base):**

```lean
theorem T {x y : ℝ}⟦⟧ (hx : 0 < x)
    (hxy : x * y = 1 / 9) (hxy1 : x * (y + 1) = 7 / 9) (hxy2 : y * (x + 1) = 5 / 18) :
    (x + 1) * (y + 1) = 35 / 18 := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 19. D8 (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:OEIS/1146:OeisA1146.divisibility_fact` (archivo `OEIS/1146`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 2; dirección trivial: ambas; correlato en el NL: sí

**NL:**

> The forward direction: if $k = a(n)$ for $n \ge 2$, then $k^4 - 1$ divides $2^k - 1$.

**Lean original:**

```lean
theorem T (n : ℕ) (hn : 2 ≤ n) : (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ) := by
  sorry
```

**Variante (D8; edición respecto al original):**

```lean
theorem T (n : ℕ) (hn : ⟦1 < n⟧) : (((a n)^4 - 1) : ℕ) ∣ (2^(a n) - 1 : ℕ) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 20. C2∘D1 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[77]` (archivo `FormalMATH_lite[77]`; FormalMATH-Lite); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 5; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> A town has an initial population of $80\ 000$. It grows at a constant rate of $2200$ per year for $5$ years. The linear function that models the town’s population $P$ as a function of the year is: $P(t) = 80\ 000 + 2200 \cdot t$, where $t$ is the number of years since the model began. When will the population reach $120\ 000$?
>  Prove that the answer is: $t$: $\frac{200}{11}$

**Lean original:**

```lean
theorem T (t : ℝ) (ht : 0 ≤ t) :
    80000 + 2200 * t = 120000 ↔ t = 200 / 11 := by
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem T (t : ℝ) (ht : ⟦t ≥ 0⟧) :
    80000 + 2200 * t = 120000 ↔ t = 200 / 11 := by
```

**Variante infiel (C2∘D1; edición respecto a la base):**

```lean
theorem T (t : ℝ) (ht : t ≥ 0) :
    80000 + ⟦2201⟧ * t = 120000 ↔ t = 200 / 11 := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 21. C2∘D8 (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Paper/StrongSensitivityConjecture:StrongSensitivityConjecture.nisanExample_blockSensitivity` (archivo `Paper/StrongSensitivityConjecture`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> Assuming `n` is a multiple of 4 and $n \ge 8$, the block sensitivity of
> `nisanExample` is $3n/4$, achieved by any $x$ with Hamming weight $n/2$.
> An optimal block configuration uses all $n/2$ one-bits as singleton blocks
> and forms $n/4$ disjoint size-2 blocks from the zero-bits.

**Lean original:**

```lean
theorem T (n : ℕ) (hn : 4 ∣ n) (hn_large : 8 ≤ n) :
    blockSensitivity (nisanExample n) = 3 * n / 4 := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T (n : ℕ) (hn : 4 ∣ n) (hn_large : ⟦7 < n⟧) :
    blockSensitivity (nisanExample n) = 3 * n / 4 := by
  sorry
```

**Variante infiel (C2∘D8; edición respecto a la base):**

```lean
theorem T (n : ℕ) (hn : ⟦5⟧ ∣ n) (hn_large : 7 < n) :
    blockSensitivity (nisanExample n) = 3 * n / 4 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 22. D1c (reescritura_fiel) — etiqueta esperada: **adecuada**

- Origen: `formal_conjectures:Wikipedia/Falconer:Falconer.falconer_conjecture_two` (archivo `Wikipedia/Falconer`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 6; dirección trivial: ambas; correlato en el NL: no

**NL:**

> Falconer's distance set conjecture, $d = 2$ case.
> 
> This was proved by an internal OpenAI model in September 2026 [OAI26a]; see the linked Lean
> proof.

**Lean original:**

```lean
theorem T (E : Set <| ℝ²) (hc : IsCompact E) (hd : 2 < 2 * dimH E ) :
    0 < volume (image2 dist E E) := by
  sorry
```

**Variante (D1c; edición respecto al original):**

```lean
theorem T (E : Set <| ℝ²) (hc : IsCompact E) (hd : 2 < 2 * dimH E ) :
    ⟦volume (image2 dist E E) > 0⟧ := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 23. A3∘D1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Books/BugeaudDistributionModuloOne/Problem10_5:Bugeaud05.problem_10_5` (archivo `Books/BugeaudDistributionModuloOne/Problem10_5`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 4; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Problem 10.5 (first part). Let $\mathbb{K}$ be a real number field. Then, for any
> $\varepsilon > 0$, there exists a lacunary sequence $(t_n)_{n \ge 1}$ of positive numbers
> in $\mathbb{K}$ such that
> $$\limsup_{n \to \infty} \{\xi t_n\} \ge 1 - \varepsilon,$$
> for any real number $\xi$ not in $\mathbb{K}$.
> 
> This follows from the stronger `problem_10_5_moreover` via
> `problem_10_5_of_moreover`. A Lean 4 formalization by Kenta Kitamura
> ([KitaKen1 on GitHub](https://github.com/KitaKen1)) is available at
> [KitaKen1/bugeaud-10-5-lacunary](https://github.com/KitaKen1/bugeaud-10-5-lacunary).

**Lean original:**

```lean
theorem T (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K →
        (1 - ε) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem T (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : ⟦ε > 0⟧) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K →
        (1 - ε) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
  sorry
```

**Variante infiel (A3∘D1; edición respecto a la base):**

```lean
theorem T (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K]
    {ε : ℝ} (hε : ε ⟦≥⟧ 0) :
    ∃ t : ℕ → K, (∀ n, 0 < (t n : ℝ)) ∧
      IsLacunaryReal (fun k => (t k : ℝ)) ∧
      ∀ ξ : ℝ, ξ ∉ K →
        (1 - ε) ≤ limsup (fun n => Int.fract (ξ * (t n : ℝ))) atTop := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 24. C3∘D1c (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[88]` (archivo `FormalMATH_lite[88]`; FormalMATH-Lite); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 20; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> Let \(A\), \(B\), \(C\) be the three interior angles of a triangle. Prove that:
> \[
> \sin3A+\sin3B + \sin3C\leqslant\frac{3}{2}\sqrt{3}
> \]

**Lean original:**

```lean
open Real Set
open scoped Real

theorem T (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  sin (3 * A) + sin (3 * B) + sin (3 * C) ≤ 3 * sqrt 3 / 2 := by
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
open Real Set
open scoped Real

theorem T (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  ⟦3 * sqrt 3 / 2 ≥ sin (3 * A) + sin (3 * B) + sin (3 * C)⟧ := by
```

**Variante infiel (C3∘D1c; edición respecto a la base):**

```lean
open Real Set
open scoped Real

theorem T (A B C : Real) (hA : A ∈ Ioo 0 π)
  (hB : B ∈ Ioo 0 π) (hC : C ∈ Ioo 0 π) (hABC : A + B + C = π) :
  3 * sqrt 3 / 2 ⟦≤⟧ sin (3 * A) + sin (3 * B) + sin (3 * C) := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 25. B4∘D4c (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:OEIS/341254:OeisA341254.a_bounds` (archivo `OEIS/341254`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 27; respecto a la base fiel: 25; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> Conjecture: $1/4 < n r^2 - a(n) < 3$ for $n \ge 1$, where $r = (2 + \sqrt{5})/2$.
> 
> A formal proof has been found with the methods described in
> [arxiv/2605.22763](https://arxiv.org/abs/2605.22763).

**Lean original:**

```lean
theorem T (n : ℕ) (hn : 1 ≤ n) : (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ) ∧
    (n : ℝ) * rSq - (a n : ℝ) < 3 := by
  sorry
```

**Variante fiel (base D4c, la otra mitad del par; edición respecto al original):**

```lean
theorem T (n : ℕ) (hn : 1 ≤ n) : ⟦(n : ℝ) * rSq - (a n : ℝ) < 3 ∧ (1 / 4 : ℝ) < (n : ℝ) * rSq - (a n : ℝ)⟧ := by
  sorry
```

**Variante infiel (B4∘D4c; edición respecto a la base):**

```lean
theorem T (n : ℕ) (hn : 1 ≤ n) : ⟦(n : ℝ) * rSq - (a n : ℝ) < 3⟧ := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 26. A2∘D1c (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Other/SuffixPrefixAvoidance:SuffixPrefixAvoidance.suffix_prefix_avoidance_bound` (archivo `Other/SuffixPrefixAvoidance`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 20; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> $A$ and $B$ are sets of words of length $n$ over alphabet with $q \geq 1$ letters.
> No suffix of a word in $A$ coincides with a prefix of a word in $B$.
> Then $|A| \cdot |B|$ is at most $\frac{q^{2n}}{en}$.
> 
> This problem is from *Maximal sets of strings with no prefix-suffix overlap* and was proved in
> *An isoperimetric inequality for word overlap*.

**Lean original:**

```lean
theorem T
    (A B : Finset (Fin n → Fin q))
    (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n) := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem T
    (A B : Finset (Fin n → Fin q))
    (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    ⟦(q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card⟧ := by
  sorry
```

**Variante infiel (A2∘D1c; edición respecto a la base):**

```lean
theorem T
    (A B : Finset (Fin n → Fin q))
    (hq : 0 < q) (hn : 0 < n)
    (h : IsSuffixPrefixAvoiding A B) :
    (q : ℝ) ^ (2 * n) / (exp 1 * n) ⟦>⟧ (A.card : ℝ) * B.card := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 27. B3∘D8 (mas_debil) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:ErdosProblems/835:Erdos835.johnsonGraph_2k_k_chromaticNumber_known_cases` (archivo `ErdosProblems/835`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 3; respecto a la base fiel: 1; dirección trivial: original ⇒ variante; correlato en el NL: sí

**NL:**

> It is known that for $3 \leq k \leq 8$, the chromatic number of $J(2k, k)$ is greater than $k+1$,
> see [Johnson graphs](https://aeb.win.tue.nl/graphs/Johnson.html).

**Lean original:**

```lean
theorem T (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 8) :
    J(2 * k, k).chromaticNumber > k + 1 := by
  sorry
```

**Variante fiel (base D8, la otra mitad del par; edición respecto al original):**

```lean
theorem T (k : ℕ) (hk : ⟦2 < k⟧) (hk' : k ≤ 8) :
    J(2 * k, k).chromaticNumber > k + 1 := by
  sorry
```

**Variante infiel (B3∘D8; edición respecto a la base):**

```lean
theorem T (k : ℕ) (hk : 2 < k) (hk' : k ⟦<⟧ 8) :
    J(2 * k, k).chromaticNumber > k + 1 := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 28. A3∘D1c (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `FormalMATH_lite[288]` (archivo `FormalMATH_lite[288]`; FormalMATH-Lite); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 23; respecto a la base fiel: 1; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> Let \(a,b,c\in\mathbf{R}^{+}\), prove that:
> \[
> \frac{1}{a^{3}+b^{3}+abc}+\frac{1}{b^{3}+c^{3}+abc}+\frac{1}{c^{3}+a^{3}+abc}\leq\frac{1}{abc}
> \]

**Lean original:**

```lean
theorem T (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a^3 + b^3 + a * b * c) + 1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c) ≤ 1 / (a * b * c) := by
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem T (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ⟦1 / (a * b * c) ≥ 1 / (a^3 + b^3 + a * b * c) + 1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c)⟧ := by
```

**Variante infiel (A3∘D1c; edición respecto a la base):**

```lean
theorem T (a b c : ℝ) (ha : 0 ⟦≤⟧ a) (hb : 0 < b) (hc : 0 < c) :
    1 / (a * b * c) ≥ 1 / (a^3 + b^3 + a * b * c) + 1 / (b^3 + c^3 + a * b * c) +
    1 / (c^3 + a^3 + a * b * c) := by
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 29. C2∘D1c (otro_teorema) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Wikipedia/TuzaConjecture:TuzaConjecture.tuza_conjecture.variants.haxell` (archivo `Wikipedia/TuzaConjecture`; formal_conjectures); zona: conclusion; tokens editados respecto al original (Qwen3-4B): 19; respecto a la base fiel: 1; dirección trivial: ninguna; correlato en el NL: sí

**NL:**

> Haxell (1999): every finite graph satisfies $\tau(G) \le (66/23)\nu(G)$.
> 
> *Reference:* [Ha99].

**Lean original:**

```lean
theorem T {V : Type} [Fintype V] (G : SimpleGraph V) :
    (triangleCoverNumber G : ℝ) ≤ 66 / 23 * trianglePackingNumber G := by
  sorry
```

**Variante fiel (base D1c, la otra mitad del par; edición respecto al original):**

```lean
theorem T {V : Type} [Fintype V] (G : SimpleGraph V) :
    ⟦66 / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ)⟧ := by
  sorry
```

**Variante infiel (C2∘D1c; edición respecto a la base):**

```lean
theorem T {V : Type} [Fintype V] (G : SimpleGraph V) :
    ⟦67⟧ / 23 * trianglePackingNumber G ≥ (triangleCoverNumber G : ℝ) := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:

## 30. A1∘D1 (mas_fuerte) — etiqueta esperada: **inadecuada**

- Origen: `formal_conjectures:Books/BugeaudDistributionModuloOne/Problem10_6:Bugeaud06.hasIntermediateGrowth_of_isGenuinelySublacunary` (archivo `Books/BugeaudDistributionModuloOne/Problem10_6`; formal_conjectures); zona: hipotesis; tokens editados respecto al original (Qwen3-4B): 14; respecto a la base fiel: 10; dirección trivial: variante ⇒ original; correlato en el NL: sí

**NL:**

> **A ratio floor implies intermediate growth**, at every exponent $\alpha < 1$. So the
> ratio reading of Problem 10.6 is strictly stronger than the growth reading, and by
> `exists_dense_of_growth` it is the reading that carries the content of the problem.

**Lean original:**

```lean
theorem T {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    HasIntermediateGrowth α m := by
  sorry
```

**Variante fiel (base D1, la otra mitad del par; edición respecto al original):**

```lean
theorem T {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : ⟦α > 0⟧) (hα1 : α < 1) :
    HasIntermediateGrowth α m := by
  sorry
```

**Variante infiel (A1∘D1; edición respecto a la base):**

```lean
theorem T {m : ℕ → ℕ}
    (h : IsGenuinelySublacunary m) {α : ℝ} (hα0 : α > 0)⟦⟧ :
    HasIntermediateGrowth α m := by
  sorry
```

Revisión: ☐ P0 original fiel al NL  ☐ P1 etiqueta correcta  ☐ P2 variante sensata — comentario:
