import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Erdős–Moser equation

For positive integers $k$ and $m$, let

$$S_k(m)=1^k+2^k+\cdots+(m-1)^k.$$

The Erdős–Moser conjecture says that $S_k(m)=m^k$ has only the solution
$(k,m)=(1,3)$.

*References:*
* [Wikipedia: Erdős–Moser equation](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Moser_equation)
* B. C. Kellner,
  [On stronger conjectures that imply the Erdős–Moser conjecture](https://arxiv.org/abs/1003.1646)
-/

section

namespace ErdosMoser

/-- The power sum $S_k(m)=\sum_{i=1}^{m-1} i^k$. -/
def powerSum (k m : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico 1 m, i ^ k

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 = 5

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 = 5)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 = 5)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 3 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔
    (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔
    (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔
    (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔
    (powerSum 2 3 ≠ 3 ^ 2 ∧ powerSum 2 3 = 5) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  powerSum 2 3 ≠ 3 ^ 2

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) →
    (powerSum 2 3 ≠ 3 ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((powerSum 2 3 = 5 ∧ powerSum 2 3 ≠ 3 ^ 2) ↔ (powerSum 2 3 ≠ 3 ^ 2)) :=
  by decide

#eval "FIN_CERTIFICAR"
