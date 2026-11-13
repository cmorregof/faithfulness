import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open scoped BigOperators

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(4 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (5 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (0 < d) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀' : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀' : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀' : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀' : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀' : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : ¬(d ≤ 0)) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (¬(d ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : ¬(d ≤ 0)) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : ¬(d ≤ 0)) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : ¬(d ≤ 0)) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : ¬(d ≤ 0)) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) :
    (d > 0) ↔ (d ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) ↔
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(4 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (5 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : 0 < d) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 3*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₅ : 2*j+3*s+4*b=91) :
    (2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (s > 0) ∧ (2*j+3*s+4*b=91) ∧ (¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (1 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(4 : ℤ), (2 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (2 : ℤ), (5 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (1 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (3 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (4 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(2 : ℤ), (5 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (2 : ℤ), (4 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (1 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (3 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(1 : ℤ), (4 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (2 : ℤ), (3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℤ) (j : ℤ) (s : ℤ), ¬((2*b+3*j+4*s=74) ↔ (3*b+3*j+4*s=74)) :=
  ⟨(3 : ℤ), (3 : ℤ), (2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₀ : d ≥ 1) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (d b j s : ℤ) (h₁ : b > 0) (h₀ : d > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) →
    (∀ (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91), b^2+j^2+s^2=314) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    (s > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (-1 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (0 : ℤ), (1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(-1 : ℤ), (1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (0 : ℤ), (-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(1 : ℤ), (-1 : ℤ), (0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℤ) (b : ℤ) (j : ℤ) (s : ℤ), (d > 0) ∧ (b > 0) ∧ (j > 0) ∧ (2*b+3*j+4*s=74) ∧ (2*j+3*s+4*b=91) ∧ (¬((s > 0) ↔ (True))) :=
  ⟨(0 : ℤ), (0 : ℤ), (1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(-2 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (s : ℤ), ¬((s > 0) ↔ (True)) :=
  ⟨(3 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (d b j s : ℤ) (h₀ : d > 0) (h₁ : b > 0) (h₂ : j > 0) (h₃ : s > 0) (h₄ : 2*b+3*j+4*s=74) (h₅ : 2*j+3*s+4*b=91) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
