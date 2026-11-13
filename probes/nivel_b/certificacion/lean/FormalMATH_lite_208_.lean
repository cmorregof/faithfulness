import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (y ≠ 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (20 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(20 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (20 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (19 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (20 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (z ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((y ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y ≠ 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y ≠ 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y ≠ 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y ≠ 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y ≠ 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (y : ℝ), ¬((y ≠ 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 21 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxz : x = 50 / 100 * z) :
    (x = 20 / 100 * y) ↔ (x = 21 / 100 * y) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (0 : ℝ), (50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (50 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(50 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (0 : ℝ), (49 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (50 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(0 : ℝ), (49 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (50 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(-1 : ℝ), (50 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (z ≠ 0) ∧ (x = 50 / 100 * z) ∧ (¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(21 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(21 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(100 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(21 : ℝ), (21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(100 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(99 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (101 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(21 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(100 : ℝ), (21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(99 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(101 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (22 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (101 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(21 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(100 : ℝ), (100 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(99 : ℝ), (21 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(101 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(22 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(20 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(19 : ℝ), (22 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(21 : ℝ), (101 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ), ¬((x = 20 / 100 * y) ↔ (x = 21 / 100 * y)) :=
  ⟨(100 : ℝ), (99 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : ¬(y = 0)) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y z : ℝ} :
    (y ≠ 0) ↔ (¬(y = 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy : ¬(y = 0)) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy : ¬(y = 0)) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy : ¬(y = 0)) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy : ¬(y = 0)) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hz : z ≠ 0) (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hz : z ≠ 0) (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy₀ : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy₀ : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy₀ : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy₀ : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) ↔
    (∀ {x y z : ℝ} (hy₀ : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) →
    (∀ {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z), z = 40 / 100 * y) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    (z ≠ 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (20 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(20 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (19 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (-1 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (20 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(0 : ℝ), (19 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (0 : ℝ), (20 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(-1 : ℝ), (20 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℝ) (y : ℝ) (z : ℝ), (y ≠ 0) ∧ (x = 20 / 100 * y) ∧ (x = 50 / 100 * z) ∧ (¬((z ≠ 0) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (z : ℝ), ¬((z ≠ 0) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (z : ℝ), ¬((z ≠ 0) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (z : ℝ), ¬((z ≠ 0) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (z : ℝ), ¬((z ≠ 0) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (z : ℝ), ¬((z ≠ 0) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (z : ℝ), ¬((z ≠ 0) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℝ} (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x = 20 / 100 * y) (hxz : x = 50 / 100 * z) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
