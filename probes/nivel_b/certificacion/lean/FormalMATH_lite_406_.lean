import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(2 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(4 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (True))) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (0 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(2 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(4 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (0 ≤ a))) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (0 ≤ a)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(3 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(3 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(4 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (2 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(2 : ℤ), (5 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(1 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(3 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (2 ≤ a)) :=
  ⟨(3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(4 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (4 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (3 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (6 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(6 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (6 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (6 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (a > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (h1 : a - b + c = 4) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (h1 : a - b + c = 4) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4 ∧ 2 ≤ a

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4 ∧ 2 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4 ∧ 2 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4 ∧ 2 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4 ∧ 2 ≤ a) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4 ∧ 2 ≤ a) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha₀ : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha₀ : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha₀ : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha₀ : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha₀ : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : ¬(a ≤ 0)) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (¬(a ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : ¬(a ≤ 0)) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : ¬(a ≤ 0)) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : ¬(a ≤ 0)) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : ¬(a ≤ 0)) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) :
    (0 < a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) ↔
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a ≥ 0) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (a ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(2 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(4 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (a ≥ 0))) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (a ≥ 0)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : a > 0) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(4 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (4 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (3 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (6 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(6 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (6 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (6 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c ≥ 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) :
    (b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(4 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (0 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (4 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(0 : ℤ), (3 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(-1 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0))) :=
  ⟨(1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(3 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(3 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(4 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (2 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(2 : ℤ), (5 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(1 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(3 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((b ^ 2 - 4 * a * c > 0) ↔ (b ^ 2 - 4 * a * c ≥ 0)) :=
  ⟨(3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (0 < a) ↔ (1 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(2 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(4 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(3 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (a - b + c = 4) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((0 < a) ↔ (1 < a))) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ), ¬((0 < a) ↔ (1 < a)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 1 ≤ a) (h1 : a - b + c = 5) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    (a - b + c = 4) ↔ (a - b + c = 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(4 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (0 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (4 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(0 : ℤ), (3 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(-1 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), (0 < a) ∧ (4 * a + 2 * b + c = 1) ∧ (b ^ 2 - 4 * a * c > 0) ∧ (¬((a - b + c = 4) ↔ (a - b + c = 5))) :=
  ⟨(1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (6 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (3 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(6 : ℤ), (4 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (4 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (3 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (5 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (6 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(4 : ℤ), (0 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (4 : ℤ), (6 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (3 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (5 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(3 : ℤ), (6 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (4 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((a - b + c = 4) ↔ (a - b + c = 5)) :=
  ⟨(5 : ℤ), (5 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), 2 ≤ a ∧ b + c ≤ -4) →
    (∀ (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0), b + c ≤ -4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(3 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(3 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(4 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (2 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(2 : ℤ), (5 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(1 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(3 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℤ) (b : ℤ) (c : ℤ), ¬((2 ≤ a ∧ b + c ≤ -4) ↔ (b + c ≤ -4)) :=
  ⟨(3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b c : ℤ) (ha : 0 < a) (h1 : a - b + c = 4) (h2 : 4 * a + 2 * b + c = 1) (h3 : b ^ 2 - 4 * a * c > 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
