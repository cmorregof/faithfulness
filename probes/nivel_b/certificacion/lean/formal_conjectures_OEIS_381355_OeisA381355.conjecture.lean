import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# A logarithmic derivative with prime-divisible coefficients

Let $F(x)$ be the generating function of A381353, with $F(0)=1$, $[x]F(x)=1$, and
$[x^n]F(x)^{p_n}=0$ for $n>1$, where $p_n$ is the $n$-th prime.
The sequence is defined by $\sum_{n\ge1}a(n)x^n=xF'(x)/F(x)$.

*References:*
- [A381355](https://oeis.org/A381355)
- [A381353](https://oeis.org/A381353)
- [Li26] Wentao Li, [Prime divisibility of logarithmic-derivative coefficients](https://github.com/VictorLiwentao/lean-oeis-proofs/blob/0a23974e54b90afd1453ef02c27cf8f617bad940/proofs/new-proofs/A381355/PROOF.md), 2026.
-/

section

namespace OeisA381355

open PowerSeries

/-- The $n$-th prime, indexed from $p_1=2$. -/
noncomputable def primeN (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The coefficients of $F$, obtained successively from $[x^n]F(x)^{p_n}=0$. -/
noncomputable def f : ℕ → ℤ :=
  Nat.strongRec fun n ih =>
    if n = 0 then 1
    else if n = 1 then 1
    else
      -(coeff n
          (PowerSeries.mk (fun k => if h : k < n then ih k h else 0) ^ primeN n) /
        (primeN n : ℤ))

/-- The generating function of A381353. -/
noncomputable def series : PowerSeries ℤ := PowerSeries.mk f

/-- The coefficients of $xF'(x)/F(x)$. -/
noncomputable def a (n : ℕ) : ℤ :=
  coeff n (X * derivative (R := ℤ) series * invOfUnit series 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
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
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (n > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : n > 1), (primeN n : ℤ) ∣ a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : n > 1), (primeN n : ℤ) ∣ a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : n > 1), (primeN n : ℤ) ∣ a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : n > 1), (primeN n : ℤ) ∣ a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), (primeN n : ℤ) ∣ a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), (primeN n : ℤ) ∣ a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), (primeN n : ℤ) ∣ a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn₀ : 1 < n), (primeN n : ℤ) ∣ a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 1)), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (¬(n ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), (primeN n : ℤ) ∣ a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), (primeN n : ℤ) ∣ a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), (primeN n : ℤ) ∣ a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 1)), (primeN n : ℤ) ∣ a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (primeN n : ℤ) ∣ a n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (primeN n : ℤ) ∣ a n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (primeN n : ℤ) ∣ a n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) ↔
    (∀ (n : ℕ) (hn : 2 ≤ n), (primeN n : ℤ) ∣ a n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (n ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
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
  ∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), (primeN n : ℤ) ∣ a n) →
    (∀ (n : ℕ) (hn : 2 < n), (primeN n : ℤ) ∣ a n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 < n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
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
example (n : ℕ) (hn : 1 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
