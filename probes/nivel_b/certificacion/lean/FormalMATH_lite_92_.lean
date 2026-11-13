import Mathlib
import Mathlib.Tactic
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(4 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(4 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (True))) :=
  ⟨(4 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k ≤ 100) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(4 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(4 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(4 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(4 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k ≤ 100))) :=
  ⟨(4 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k ≤ 100)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(0 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (0 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (1 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (50 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(50 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (50 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (49 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (50 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (100 > k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hm : 0 < m) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hm : 0 < m) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hm : 0 < m) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hm : 0 < m) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hm : 0 < m) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk₀ : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk₀ : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk₀ : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk₀ : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk₀ : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : ¬(100 ≤ k)) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (¬(100 ≤ k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : ¬(100 ≤ k)) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : ¬(100 ≤ k)) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : ¬(100 ≤ k)) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : ¬(100 ≤ k)) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) :
    (k < 100) ↔ (k ≤ 99) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) ↔
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 ≥ k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (100 ≥ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (100 ≥ k))) :=
  ⟨(4 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (100 ≥ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : 100 > k) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(0 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (0 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (1 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (50 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(50 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (50 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (49 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (50 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (k < 100) ↔ (k < 99) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(4 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(4 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(4 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(4 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(4 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((k < 100) ↔ (k < 99))) :=
  ⟨(4 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(98 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k < 100) ↔ (k < 99)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k ≤ 99) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(0 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (100 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (99 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (101 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (0 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(100 : ℕ), (1 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(99 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < m) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100))) :=
  ⟨(101 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (50 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(50 : ℕ), (4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (4 : ℕ), (49 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (3 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (50 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(4 : ℕ), (49 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (4 : ℕ), (50 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(3 : ℕ), (50 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), ¬(((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ↔ ((4 + m / n : ℝ) * 51 / 100 = 4 * 45 / 100 + m / n * k / 100)) :=
  ⟨(5 : ℕ), (5 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) →
    (∀ (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100), k + m + n = 85) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    (0 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(101 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(101 : ℕ), (100 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(101 : ℕ), (99 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (100 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (100 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (99 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (101 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (0 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(100 : ℕ), (1 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (100 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (99 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (101 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(99 : ℕ), (0 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(101 : ℕ), (100 : ℕ), (101 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(101 : ℕ), (99 : ℕ), (99 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ) (n : ℕ), (k < 100) ∧ (0 < n) ∧ (Nat.Coprime m n) ∧ ((4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) ∧ ((5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(101 : ℕ), (101 : ℕ), (100 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k m n : ℕ) (hk : k < 100) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) (hA : (4 + m / n : ℝ) * 50 / 100 = 4 * 45 / 100 + m / n * k / 100) (hB : (5 + (1 - m / n : ℝ)) * 50 / 100 = 5 * 48 / 100 + (1 - m / n : ℝ) * k / 100) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
