import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Goodman's conjecture on coefficients of $p$-valent functions

A regular (analytic) function is **$p$-valent** on the unit disk if it assumes each value at most
$p$ times there, and some value exactly $p$ times. For such a function $f(z) = \sum_{n \ge 1} b_n z^n$
(so $f(0) = 0$), **Goodman's conjecture** (1948) asserts that its coefficients satisfy
$$|b_n| \le \sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|
\qquad (n > p).$$
This generalises the classical coefficient bounds for univalent functions (the case $p = 1$,
where the bound reads $|b_n| \le n\,|b_1|$, i.e. $|b_n| \le n$ under the classical normalisation
$b_1 = 1$) to $p$-valent functions. It has been verified in several special cases, including
$p$-valent typically-real functions.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Goodman%27s_conjecture)
- Goodman, A. W., *On some determinants related to $p$-valent functions*,
  Trans. Amer. Math. Soc. 63 (1948), 175–192.
-/

section

open Complex Set

namespace GoodmanConjecture

/-- A function `f : ℂ → ℂ` is **$p$-valent** on the open unit disk $\mathbb{D} = \{z : |z| < 1\}$
if it is analytic there, attains every value at most $p$ times, and attains some value exactly
$p$ times. Here $p \ge 1$.
Values are counted at distinct points. For a non-constant analytic function this agrees with
counting with multiplicity: near a point where $f - w$ has a zero of order $m$, every value close
to $w$ is attained at $m$ distinct points, so the maximal number of distinct preimages equals the
maximal number of preimages counted with multiplicity. -/
structure IsPValent (f : ℂ → ℂ) (p : ℕ) : Prop where
  one_le_p   : 1 ≤ p
  analyticOn : AnalyticOn ℂ f (Metric.ball 0 1)
  /-- Every value $w$ is attained at most $p$ times on the disk. -/
  atMost     : ∀ w : ℂ, {z ∈ Metric.ball 0 1 | f z = w}.encard ≤ p
  /-- Some value $w$ is attained exactly $p$ times on the disk. -/
  exactly    : ∃ w : ℂ, {z ∈ Metric.ball 0 1 | f z = w}.encard = p

/-- The $n$-th Taylor coefficient of $f$ at $0$, i.e. $b_n = f^{(n)}(0) / n!$. -/
noncomputable def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

/-- Goodman's normalisation $f(z) = \sum_{n \ge 1} b_n z^n$, i.e. $f(0) = 0$. -/
structure IsNormalized (f : ℂ → ℂ) : Prop where
  map_zero   : f 0 = 0

/-- The Goodman bound
$$\sum_{k=1}^{p} \frac{2k (n+p)!}{(p-k)!\,(p+k)!\,(n-p-1)!\,(n^2-k^2)} |b_k|,$$
the conjectured upper bound for $|b_n|$. -/
noncomputable def goodmanBound (f : ℂ → ℂ) (p n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 p,
    (2 * k * (n + p).factorial : ℝ) /
      ((p - k).factorial * (p + k).factorial * (n - p - 1).factorial * ((n : ℝ) ^ 2 - k ^ 2)) *
      ‖coeff f k‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : n > 1), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n > 1), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n > 1), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n > 1), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n > 1), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn₀ : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn₀ : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn₀ : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn₀ : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn₀ : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : ¬(n ≤ 1)), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : ¬(n ≤ 1)), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : ¬(n ≤ 1)), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : ¬(n ≤ 1)), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : ¬(n ≤ 1)), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) ↔
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : n ≥ 1), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (n ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (n ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 2 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n), goodmanBound f 1 n = n * ‖coeff f 1‖) →
    (∀ (f : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n), goodmanBound f 1 n = n * ‖coeff f 1‖) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ)  :
    (1 < n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 < n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 < n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (f : ℂ → ℂ) (n : ℕ) (hn : 1 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
