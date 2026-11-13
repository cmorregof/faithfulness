import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 980

*References:*
- [erdosproblems.com/980](https://www.erdosproblems.com/980)
- [El67b] Elliott, P. D. T. A., *A problem of Erdős concerning power residue sums*.
  Acta Arith. 13 (1967/68), 131-149.
- [Er61e] Erdős, P., *Remarks on number theory. I*. Mat. Lapok (1961), 10-17.
- [Er65b] Erdős, P., *Some recent advances and current problems in number theory*. Lectures on
  Modern Mathematics, Vol. III (1965), 196-244.
- [MaPo11] Martin, G. and Pollack, P., *The average least character nonresidue and further
  variations on a theme of Erdős*. [arXiv:1112.1175](https://arxiv.org/abs/1112.1175) (2011).
-/

section

open Filter Asymptotics

namespace Erdos980

/-- $n_k(p)$: the least positive integer which is not a $k$-th power residue modulo $p$. If every
integer is a $k$-th power residue (for example if $\gcd(k, p - 1) = 1$) the value is $0$; this
does not happen for the primes $p \equiv 1 \pmod k$ with $k \geq 2$ used below. -/
noncomputable def leastNonresidue (k p : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ¬ ∃ x : ZMod p, x ^ k = (n : ZMod p)}

/-- $\sum n_k(p)$ over the primes $p < x$ with $p \equiv 1 \pmod k$. -/
noncomputable def residueSum (k : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % k = 1), (leastNonresidue k p : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔ (∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c₁ > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c₁ * x / Real.log x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 2)), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (¬(k < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (2 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 1 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 1 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 1 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) ↔
    (∀ (k : ℕ) (hk : 1 < k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k > 2), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : k ≥ 3), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) →
    (∀ (k : ℕ) (hk : 2 ≤ k), ∃ c > (0 : ℝ), residueSum k ~[atTop] fun x ↦ c * x / Real.log x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (2 ≤ k) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((2 ≤ k) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 2 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
