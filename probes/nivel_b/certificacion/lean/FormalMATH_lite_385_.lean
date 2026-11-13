import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (l > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(181 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(181 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1000 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(181 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1000 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(999 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (k > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((l > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((l > 0) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((l > 0) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((l > 0) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((l > 0) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((l > 0) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ), ¬((l > 0) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3002 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3002 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2002 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3002 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2002 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2001 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3002 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2002 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2001 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2003 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3002 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2002 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2001 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2003 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(0 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3001 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3000 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(3002 : ℕ), (2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (l = 3001)) :=
  ⟨(2002 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  simp_all

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(180 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(360 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(359 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(361 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(90 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(89 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(91 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(182 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (0 < l) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hk : k > 0) (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hk : k > 0) (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hk : k > 0) (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hk : k > 0) (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hk : k > 0) (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002 ∧ l = 3001

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l = 3001 ∧ k = 2002) ↔ (k = 2002 ∧ l = 3001) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002 ∧ l = 3001) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002 ∧ l = 3001) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002 ∧ l = 3001) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002 ∧ l = 3001) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl₀ : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl₀ : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl₀ : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl₀ : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl₀ : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : ¬(l ≤ 0)) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (¬(l ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : ¬(l ≤ 0)) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : ¬(l ≤ 0)) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : ¬(l ≤ 0)) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : ¬(l ≤ 0)) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} :
    (l > 0) ↔ (l ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) ↔
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : 0 < l) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  simp_all

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(180 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(360 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(359 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(361 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(90 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(89 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(91 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(182 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l ≥ 1) (hk : k > 0) (h : k * 181 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  simp_all

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h' : 3 * k = 2 * l + 4) :
    (k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(180 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(0 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(1 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k > 0) ∧ (3 * k = 2 * l + 4) ∧ (¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(360 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(359 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(361 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(90 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(89 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(91 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(182 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k * 180 = 1000 * 360 + 4 * 90) ↔ (k * 181 = 1000 * 360 + 4 * 90)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    (k > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(181 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(181 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1000 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (179 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(181 : ℕ), (180 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1000 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(999 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(180 : ℕ), (1000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), (l > 0) ∧ (k * 180 = 1000 * 360 + 4 * 90) ∧ (3 * k = 2 * l + 4) ∧ (¬((k > 0) ↔ (True))) :=
  ⟨(179 : ℕ), (181 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 0) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 0) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 0) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 0) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 0) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 0) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), l = 3001 ∧ k = 2002) →
    (∀ {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4), k = 2002) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3002 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3002 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2002 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3002 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2002 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2001 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3002 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2002 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2001 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2003 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3002 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2002 : ℕ), (2002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2001 : ℕ), (3002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2003 : ℕ), (3000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(0 : ℕ), (3001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3001 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3000 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(3002 : ℕ), (2003 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (l : ℕ) (k : ℕ), ¬((l = 3001 ∧ k = 2002) ↔ (k = 2002)) :=
  ⟨(2002 : ℕ), (2001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {l k : ℕ} (hl : l > 0) (hk : k > 0) (h : k * 180 = 1000 * 360 + 4 * 90) (h' : 3 * k = 2 * l + 4) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
