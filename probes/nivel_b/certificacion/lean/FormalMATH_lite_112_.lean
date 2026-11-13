import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(25 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(25 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(11 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(12 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (26 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(12 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(26 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (26 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (0 < x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hy : y > 0) (hx : x > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hy : y > 0) (hx : x > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hy : y > 0) (hx : x > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hy : y > 0) (hx : x > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hy : y > 0) (hx : x > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx₀ : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx₀ : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx₀ : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx₀ : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx₀ : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : ¬(x ≤ 0)) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : ¬(x ≤ 0)) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : ¬(x ≤ 0)) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : ¬(x ≤ 0)) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : ¬(x ≤ 0)) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} :
    (x > 0) ↔ (x ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) ↔
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : 0 < x) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(25 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(25 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(11 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(12 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (26 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(12 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(26 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (26 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11), max x y - min x y = 5) →
    (∀ {x y : ℤ} (hx : x ≥ 1) (hy : y > 0) (hxy : x * y = 25 ∧ x + y = 11), max x y - min x y = 5) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    (x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(25 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(23 : ℤ), (1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(25 : ℤ), (-1 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(11 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(0 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(-1 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(1 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), (x > 0) ∧ (y > 0) ∧ (¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11))) :=
  ⟨(24 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(12 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (26 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (11 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(10 : ℤ), (25 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(12 : ℤ), (23 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(26 : ℤ), (24 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(24 : ℤ), (0 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(23 : ℤ), (26 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(25 : ℤ), (12 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℤ) (y : ℤ), ¬((x * y = 24 ∧ x + y = 11) ↔ (x * y = 25 ∧ x + y = 11)) :=
  ⟨(11 : ℤ), (10 : ℤ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y : ℤ} (hx : x > 0) (hy : y > 0) (hxy : x * y = 24 ∧ x + y = 11) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
