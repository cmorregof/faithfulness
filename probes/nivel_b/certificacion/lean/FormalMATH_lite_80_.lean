import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (4 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (4 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 5 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (5 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (5 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : n ≥ 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    ((∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔ ((∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a₁ b : Fin n, a₁ ≠ b → W a₁ b = 1 ∨ W a₁ b = -1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn₀ : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 4)) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (¬(n < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : ¬(n < 4)) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) :
    (4 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 3 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 3 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 3 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) ↔
    (∀ (n : ℕ) (hn : 3 < n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n > 4) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n > 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n > 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : n ≥ 5) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (n ≥ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (n ≥ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) →
    (∀ (n : ℕ) (hn : 4 ≤ n) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card), (∀ a b : Fin n, a ≠ b → W a b = 1 ∨ W a b = -1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    (4 ≤ n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hn : 4 ≤ n) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hn : 4 ≤ n) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hn : 4 ≤ n) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hn : 4 ≤ n) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (W : Fin n → Fin n → ℝ) (hn : 4 ≤ n) (hW : ∀ A B C : Finset (Fin n), A ∪ B ∪ C = Finset.univ ∧ A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅ → ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, W a b * W b c = A.card * B.card * C.card) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
