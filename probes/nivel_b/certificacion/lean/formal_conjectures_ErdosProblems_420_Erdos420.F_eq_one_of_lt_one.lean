import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 420

*References:*
- [erdosproblems.com/420](https://www.erdosproblems.com/420)
- [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
  theory*. Monographies de L'Enseignement Mathematique (1980).
- [EGIP96] Erdős, P. and Graham, S. W. and Ivić, A. and Pomerance, C., *On the number of divisors
  of $n!$*. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995), Progr. Math. 138, Birkhäuser
  Boston (1996), 337-355.

In the solved variants, $K(n)$ is the least $K \geq 1$ with $\tau((n+K)!) \geq 2\tau(n!)$, so that
$K(n) > h$ if and only if $F(h, n) < 2$. These variants state Corollaries 2 and 3 of [EGIP96] as
printed; the stronger claims on erdosproblems.com are not stated.
-/

section

open Filter
open scoped ArithmeticFunction.sigma

namespace Erdos420

/--
`F f n` is
$$F(f,n)=\frac{\tau((n+\lfloor f(n)\rfloor)!)}{\tau(n!)},$$
where $\tau = \sigma_0$ counts divisors. We use the natural floor `⌊f n⌋₊`, which agrees with
$\lfloor f(n) \rfloor$ when $f(n) \geq 0$ and is $0$ when $f(n) < 0$.
-/
noncomputable def F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  (σ 0 (n + ⌊f n⌋₊).factorial : ℝ) / (σ 0 n.factorial : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ}, F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n ≤ 1), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (f n ≤ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 > f n), F f n = 1

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} :
    (f n < 1) ↔ (1 > f n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 > f n), F f n = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 > f n), F f n = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 > f n), F f n = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 > f n), F f n = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf₀ : f n < 1), F f n = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf₀ : f n < 1), F f n = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf₀ : f n < 1), F f n = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf₀ : f n < 1), F f n = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) ↔
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf₀ : f n < 1), F f n = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : 1 ≥ f n), F f n = 1) →
    (∀ {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1), F f n = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ}  :
    (f n < 1) ↔ (1 ≥ f n) := by
  plausible

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {f : ℕ → ℝ} {n : ℕ} (hf : f n < 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
