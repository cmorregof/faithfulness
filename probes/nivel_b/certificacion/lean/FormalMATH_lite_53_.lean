import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Finset Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
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
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 3 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
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
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

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
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s₁ : Finset ℝ, s₁.card = n ∧ ∀ x ∈ s₁,
      ∃ t : Finset ℝ, t ⊆ s₁ ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk₀ : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 2)), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

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
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 2)), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

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
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k > 2), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
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
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : k ≥ 3), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
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
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
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
example : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) →
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 2 ≤ k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) →
    (∀ (k : ℕ) (hk : 1 < k), IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (2 ≤ k) ∧ (¬(IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 4)) ↔ (IsLeast {n | k + 1 ≤ n ∧ ∃ s : Finset ℝ, s.card = n ∧ ∀ x ∈ s,
      ∃ t : Finset ℝ, t ⊆ s ∧ t.card = k ∧ x = ∑ i ∈ t, i} (k + 5))) :=
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
