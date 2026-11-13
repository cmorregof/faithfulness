import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1013

*References:*
- [erdosproblems.com/1013](https://www.erdosproblems.com/1013)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [GrYa68] Graver, J. E. and Yackel, J., *Some graph theoretic results associated with Ramsey's
  theorem*. J. Combinatorial Theory 4 (1968), 125-175.
- [DaIl22] Davies, E. and Illingworth, F., *The $\chi$-Ramsey problem for triangle-free graphs*.
  SIAM J. Discrete Math. 36 (2022), 1124-1134.
- [HHKP25] Hefty, Z., Horn, P., King, D. and Pfender, F., *Improving $R(3,k)$ in just two bites*.
  [arXiv:2510.19718](https://arxiv.org/abs/2510.19718) (2025).
-/

section

open Filter Asymptotics

namespace Erdos1013

/-- $h_3(k)$ is the least $n$ such that some triangle-free graph on $n$ vertices has chromatic
number $k$. Triangle-free graphs of every chromatic number exist (Mycielski), so the set is
nonempty and `sInf` is a true minimum. -/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k}

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≤ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 < 1

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (h3 1 < 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(h3 1 < 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(h3 1 < 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (h3 1 < 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (h3 1 < 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≤ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≥ 1

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≥ 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (h3 1 ≥ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(h3 1 ≥ 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(h3 1 ≥ 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (h3 1 ≥ 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (h3 1 ≥ 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≤ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  1 ≥ h3 1

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (1 ≥ h3 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (1 ≥ h3 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (1 ≥ h3 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (1 ≥ h3 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (1 ≥ h3 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≤ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(1 < h3 1)

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (h3 1 ≤ 1) ↔ (¬(1 < h3 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (¬(1 < h3 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (¬(1 < h3 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (¬(1 < h3 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) ↔
    (¬(1 < h3 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≤ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  1 > h3 1

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (1 > h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(1 > h3 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(1 > h3 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (1 > h3 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (1 > h3 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  h3 1 ≤ 1

set_option maxHeartbeats 200000 in
example : Prop :=
  1 ≤ h3 1

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (1 ≤ h3 1) →
    (h3 1 ≤ 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (h3 1 ≤ 1) →
    (1 ≤ h3 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(1 ≤ h3 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(1 ≤ h3 1)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (1 ≤ h3 1)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((h3 1 ≤ 1) ↔ (1 ≤ h3 1)) :=
  by decide

#eval "FIN_CERTIFICAR"
