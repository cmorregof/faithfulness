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

noncomputable def voronovskaja_theorem.bezier_bernstein_operators.answer : ℝ → (ℝ → ℝ) → ℝ → ℝ :=
  fun a g y => bezierBias a * Real.sqrt (y * (1 - y)) * iteratedDerivWithin 1 g I y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα : α ≠ 1) :
    (0 < α) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ≠ 1) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ≠ 1) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ≠ 1) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ≠ 1) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ≠ 1) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (α ≠ 1) ∧ (¬((0 < α) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((0 < α) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : α > 0) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (α > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : α > 0) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : α > 0) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : α > 0) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : α > 0) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : ¬(α = 1)), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (α ≠ 1) ↔ (¬(α = 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : ¬(α = 1)), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : ¬(α = 1)), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : ¬(α = 1)), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : ¬(α = 1)), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα : α ≠ 1) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα : α ≠ 1) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα : α ≠ 1) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα : α ≠ 1) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα : α ≠ 1) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos₀ : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos₀ : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos₀ : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos₀ : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos₀ : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : ¬(α ≤ 0)) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (α : ℝ) :
    (0 < α) ↔ (¬(α ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : ¬(α ≤ 0)) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : ¬(α ≤ 0)) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : ¬(α ≤ 0)) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) ↔
    (∀ (α : ℝ) (hα_pos : ¬(α ≤ 0)) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (α : ℝ) (hα_pos : 0 < α), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) →
    (∀ (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1), ∀ᶠ m : ℕ in atTop,
      ∀ (f : ℝ → ℝ) (x : ℝ), x ∈ I → ContDiffOn ℝ m f I →
        Tendsto (fun n : ℕ => Real.sqrt n * (bezierBernstein n α f x - f x)) atTop
          (𝓝 (bezierBias α * Real.sqrt (x * (1 - x)) * iteratedDerivWithin 1 f I x))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) :
    (α ≠ 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (¬((α ≠ 1) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (¬((α ≠ 1) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (¬((α ≠ 1) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (¬((α ≠ 1) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (¬((α ≠ 1) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), (0 < α) ∧ (¬((α ≠ 1) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α ≠ 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α ≠ 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α ≠ 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α ≠ 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α ≠ 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (α : ℝ), ¬((α ≠ 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (α : ℝ) (hα_pos : 0 < α) (hα : α ≠ 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
