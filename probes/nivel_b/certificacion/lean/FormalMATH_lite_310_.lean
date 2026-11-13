import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

def R (x y : ℕ) := 50 * x + 100 * y + 2 * x * y - 4 * x ^ 2 - 5 * y ^ 2
def P (x y : ℕ) := 38 * x + 76 * y + 2 * x * y - 160 - 4 * x ^ 2 - 5 * y ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  R 8 10 = 804 ∧ P 8 10 = 308

set_option maxHeartbeats 200000 in
example : Prop :=
  R 8 10 = 804

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((R 8 10 = 804 ∧ P 8 10 = 308) ↔ (R 8 10 = 804)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((R 8 10 = 804 ∧ P 8 10 = 308) ↔ (R 8 10 = 804)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  R 8 10 = 804 ∧ P 8 10 = 308

set_option maxHeartbeats 200000 in
example : Prop :=
  R 9 10 = 804 ∧ P 8 10 = 308

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (R 9 10 = 804 ∧ P 8 10 = 308) →
    (R 8 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (R 9 10 = 804 ∧ P 8 10 = 308) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(R 9 10 = 804 ∧ P 8 10 = 308)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(R 9 10 = 804 ∧ P 8 10 = 308)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((R 8 10 = 804 ∧ P 8 10 = 308) ↔ (R 9 10 = 804 ∧ P 8 10 = 308)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((R 8 10 = 804 ∧ P 8 10 = 308) ↔ (R 9 10 = 804 ∧ P 8 10 = 308)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  R 8 10 = 804 ∧ P 8 10 = 308

set_option maxHeartbeats 200000 in
example : Prop :=
  P 8 10 = 308 ∧ R 8 10 = 804

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308 ∧ R 8 10 = 804) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔
    (P 8 10 = 308 ∧ R 8 10 = 804) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔
    (P 8 10 = 308 ∧ R 8 10 = 804) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔
    (P 8 10 = 308 ∧ R 8 10 = 804) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) ↔
    (P 8 10 = 308 ∧ R 8 10 = 804) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  R 8 10 = 804 ∧ P 8 10 = 308

set_option maxHeartbeats 200000 in
example : Prop :=
  P 8 10 = 308

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (R 8 10 = 804 ∧ P 8 10 = 308) →
    (P 8 10 = 308) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ¬((R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((R 8 10 = 804 ∧ P 8 10 = 308) ↔ (P 8 10 = 308)) :=
  by decide

#eval "FIN_CERTIFICAR"
