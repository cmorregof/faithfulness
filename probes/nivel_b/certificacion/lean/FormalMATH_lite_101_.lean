import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(122 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : 120 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (120 > d) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : 120 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : 120 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : 120 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : 120 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀' : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀' : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀' : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀' : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀' : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : ¬(120 ≤ d)) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (d < 120) ↔ (¬(120 ≤ d)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : ¬(120 ≤ d)) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : ¬(120 ≤ d)) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : ¬(120 ≤ d)) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : ¬(120 ≤ d)) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) :
    (m > 0) ↔ (m ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) ↔
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 120 ≥ d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (120 ≥ d) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (120 ≥ d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (120 ≥ d)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : 121 > d) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (121 > d) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (121 > d))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(122 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (121 > d)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d ≤ 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d ≤ 120) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d ≤ 120))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d ≤ 120)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (m > 0) ↔ (m > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (120 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (119 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (119 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (120 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (120 : ℤ), (121 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (119 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (121 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (119 : ℝ), (120 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (119 : ℝ), (119 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (121 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (120 : ℝ), (120 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (120 : ℝ), (119 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (119 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(121 : ℝ), (120 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (119 : ℤ), (121 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (121 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (119 : ℝ), (120 : ℤ), (121 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (119 : ℝ), (119 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (119 : ℝ), (121 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (121 : ℝ), (120 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (121 : ℝ), (119 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (120 : ℝ), (120 : ℤ), (121 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (120 : ℝ), (119 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (120 : ℝ), (121 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (119 : ℝ), (120 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (119 : ℝ), (119 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(119 : ℝ), (121 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(121 : ℝ), (120 : ℝ), (120 : ℤ), (119 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(121 : ℝ), (120 : ℝ), (119 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(121 : ℝ), (119 : ℝ), (120 : ℤ), (120 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (d < 120) ∧ (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((m > 0) ↔ (m > 1))) :=
  ⟨(120 : ℝ), (120 : ℝ), (121 : ℤ), (121 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℤ), ¬((m > 0) ↔ (m > 1)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℤ), ¬((m > 0) ↔ (m > 1)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℤ), ¬((m > 0) ↔ (m > 1)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℤ), ¬((m > 0) ↔ (m > 1)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℤ), ¬((m > 0) ↔ (m > 1)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℤ), ¬((m > 0) ↔ (m > 1)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (h₀ : d < 121) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (d < 121) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (d < 121))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(122 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (d < 121)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m ≥ 1) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d : ℝ) (r : ℝ) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) →
    (∀ (d : ℝ) (h₀ : d < 120) (r : ℝ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (m n : ℤ) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n), m + n = 174) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    (d < 120) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (179 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (179 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (181 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (180 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (179 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (180 : ℝ), (181 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (179 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(179 : ℝ), (181 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (180 : ℤ), (179 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (180 : ℝ), (179 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(181 : ℝ), (179 : ℝ), (180 : ℤ), (180 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ) (r : ℝ) (m : ℤ) (n : ℤ), (r * Real.sin (d * Real.pi / 180) = 22) ∧ (r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) ∧ (m > 0) ∧ (n > 0) ∧ (r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) ∧ (¬((d < 120) ↔ (True))) :=
  ⟨(180 : ℝ), (180 : ℝ), (181 : ℤ), (181 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(120 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(119 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(121 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℝ), ¬((d < 120) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (d : ℝ) (r : ℝ) (m n : ℤ) (h₀ : d < 120) (h₁ : r * Real.sin (d * Real.pi / 180) = 22) (h₂ : r * Real.sin (2 * d * Real.pi / 180) = r * Real.sin (3 * d * Real.pi / 180) + 20) (hm : m > 0) (hn : n > 0) (h₃ : r * Real.sin (3 * d * Real.pi / 180) = -m + Real.sqrt n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
