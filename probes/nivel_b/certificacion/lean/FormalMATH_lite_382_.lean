import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Finset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a₁ ∈ S, (2 * n + 2 - a₁) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n ≤ 0)), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : n > 0), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), {S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) →
    (∀ {n : ℕ} (hn : 1 ≤ n), {S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(({S : Set ℕ | S ⊆ Icc 1 (2 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1) ↔ ({S : Set ℕ | S ⊆ Icc 1 (3 * n + 1) ∧ S.Nonempty ∧ ∀ a ∈ S, (2 * n + 2 - a) ∈ S}.ncard = 2 ^ (n + 1) - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
