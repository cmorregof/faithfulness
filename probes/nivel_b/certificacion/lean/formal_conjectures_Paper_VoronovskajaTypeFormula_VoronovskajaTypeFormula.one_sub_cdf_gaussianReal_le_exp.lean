import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Voronovskaja-type Formula for the Bezier Variant of the Bernstein Operators

The Bézier-type Bernstein operators $B_{n,\alpha}$ for $\alpha > 0$ are defined for
$f : [0,1] \to \mathbb{R}$ by
$$
(B_{n,\alpha} f)(x)
  = \sum_{k=0}^n f\!\left(\frac{k}{n}\right)
    \left( J_{n,k}(x)^{\alpha} - J_{n,k+1}(x)^{\alpha} \right),
$$
where
$$
J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x),
\qquad
p_{n,j}(x) = \binom{n}{j} x^j(1-x)^{n-j},
$$
and $J_{n,n+1}(x) = 0$.

In the classical case $\alpha = 1$, these operators reduce to the usual Bernstein operators.
For $f$ which are $C^2$ on $[0,1]$, one has the classical Voronovskaja
asymptotic formula
$$
\lim_{n \to \infty} n\bigl( B_{n,1} f(x) - f(x) \bigr)
    = \tfrac{1}{2} x(1-x) f''(x).
$$

## Known Results
* For $\alpha = 1$, the asymptotics are completely understood.
* Numerical experiments indicate that for $\alpha \neq 1$ the quantity
    $$
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr)
    $$
    may converge to a non-zero limit.

## The Problem
Determine the asymptotic behaviour of the Bézier-type Bernstein operators for $\alpha > 0$,
$\alpha \neq 1$:
\textbf{Existence of the limit:}
    Prove (or disprove) the existence of the limit
    $$
        \lim_{n \to \infty}
        \sqrt{n}\,\bigl( B_{n,\alpha} f(x) - f(x) \bigr),
    $$
    at least for sufficiently smooth functions $f$.
    \textbf{Explicit form of the limit:}
    If the limit exists, determine an explicit expression for it in terms of $f$, $x$, and $\alpha$.

## Provenance

The limit formula recorded here, together with the elementary identities and the endpoint
reduction in this file, was first proposed by *Samuel Schlesinger*. The first complete proof
is the Lean 4 formalisation by *Kenta Kitamura*
([KitaKen1 on GitHub](https://github.com/KitaKen1)) in [K26], which is linked from
`voronovskaja_theorem.bezier_bernstein_operators`.

*References:*

* [Voronovskaja-type Formula for the Bézier Variant of the Bernstein Operators](https://www.math.bas.bg/mathmod/Proceedings_CTF/CTF-2010/files_CTF-2010/Open_problems.pdf),
  by *Ulrich Abel*, in *Constructive Theory of Functions, Sozopol 2010*.
* [K26] [A Formal Conjectures Bézier--Bernstein Theorem in
  Lean](https://github.com/KitaKen1/bezier-bernstein-voronovskaja-lean), by *Kenta Kitamura*.
-/

section

open Topology Filter MeasureTheory ProbabilityTheory Real unitInterval Polynomial

namespace VoronovskajaTypeFormula

/--
Cumulative sum $J_{n,k}(x) = \sum_{j=k}^n p_{n,j}(x)$.
-/
noncomputable def bernsteinTail (n k : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.Icc k n, bernsteinPolynomial ℝ n j

/--
Bézier–type Bernstein operator:
$$
(B_{n,\alpha} f)(x)
= \sum_{k=0}^{n}
f\!\left(\frac{k}{n}\right)
\left(
J_{n,k}(x)^{\alpha}
- J_{n,k+1}(x)^{\alpha}
\right)
$$
-/
noncomputable def bezierBernstein (n : ℕ) (α : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    f (k / n) * ((bernsteinTail n k).eval x ^ α - (bernsteinTail n (k + 1)).eval x ^ α)

/--
The proposed first-order bias constant for the Bézier--Bernstein operator:
\[
\mu_\alpha = \int_0^\infty
  \bigl((1-\Phi(t))^\alpha + \Phi(t)^\alpha - 1\bigr)\,dt.
\]
Here $\Phi$ is Mathlib's cumulative distribution function of the standard
Gaussian measure.
-/
noncomputable def bezierBias (α : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0,
    (1 - cdf (gaussianReal 0 1) t) ^ α + cdf (gaussianReal 0 1) t ^ α - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  simp_all

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (t ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht₀ : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht₀ : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht₀ : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht₀ : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht₀ : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : ¬(t < 0)), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {t : ℝ} :
    (0 ≤ t) ↔ (¬(t < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : ¬(t < 0)), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : ¬(t < 0)), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : ¬(t < 0)), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔
    (∀ {t : ℝ} (ht : ¬(t < 0)), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t < Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t > 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (t > 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (t > 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (t > 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (t > 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (t > 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (t > 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (t > 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (t > 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (t > 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (t > 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (t > 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (t > 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (t > 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 3)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : t ≥ 0), 1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (1 - cdf (gaussianReal 0 1) t ≥ Real.exp (-(t ^ 2 / 2)))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) > 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 < t), Real.exp (-(t ^ 2 / 2)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  simp_all

set_option maxHeartbeats 200000 in
example {t : ℝ}  :
    (0 ≤ t) ↔ (0 < t) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (¬((0 ≤ t) ↔ (0 < t))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((0 ≤ t) ↔ (0 < t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 3)) ≥ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) →
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {t : ℝ} (ht : 0 ≤ t), 1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) →
    (∀ {t : ℝ} (ht : 0 ≤ t), Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), (0 ≤ t) ∧ (¬(Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℝ), ¬((1 - cdf (gaussianReal 0 1) t ≤ Real.exp (-(t ^ 2 / 2))) ↔ (Real.exp (-(t ^ 2 / 2)) ≤ 1 - cdf (gaussianReal 0 1) t)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {t : ℝ} (ht : 0 ≤ t) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {t : ℝ} (ht : 0 ≤ t) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {t : ℝ} (ht : 0 ≤ t) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {t : ℝ} (ht : 0 ≤ t) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {t : ℝ} (ht : 0 ≤ t) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
