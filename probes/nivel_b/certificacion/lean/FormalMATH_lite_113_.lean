import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open scoped Affine

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (A < B) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (B < C) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((A < B) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ), ¬((A < B) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (5 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(5 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (5 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (5 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (B > A) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hB : B < C) (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hB : B < C) (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hB : B < C) (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hB : B < C) (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hB : B < C) (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA₀ : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA₀ : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA₀ : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA₀ : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA₀ : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : ¬(B ≤ A)) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} :
    (A < B) ↔ (¬(B ≤ A)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : ¬(B ≤ A)) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : ¬(B ≤ A)) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : ¬(B ≤ A)) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) ↔
    (∀ {A B C D : ℝ} (hA : ¬(B ≤ A)) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : B > A) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 6) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hBC : (C - B) / (D - C) = 2 / 1) :
    ((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (1 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (3 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (3 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (2 : ℝ), (3 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(1 : ℝ), (3 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(3 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (B < C) ∧ (C < D) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6))) :=
  ⟨(2 : ℝ), (2 : ℝ), (3 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (5 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(5 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (1 : ℝ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (0 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (5 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(1 : ℝ), (4 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (1 : ℝ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(0 : ℝ), (5 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ), ¬(((B - A) / (C - A) = 1 / 5) ↔ ((B - A) / (C - A) = 1 / 6)) :=
  ⟨(2 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) →
    (∀ {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1), (B - A) / (D - C) = 1 / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    (B < C) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (0 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(0 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(2 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(2 : ℝ), (0 : ℝ), (1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ), (A < B) ∧ (C < D) ∧ ((B - A) / (C - A) = 1 / 5) ∧ ((C - B) / (D - C) = 2 / 1) ∧ (¬((B < C) ↔ (True))) :=
  ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(0 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(0 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(0 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(-1 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(0 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(-1 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(0 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(-1 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1/2 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(0 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(-1 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(3 : ℝ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(-1 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1/2 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(3 : ℝ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(-1 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1/2 : ℝ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(3 : ℝ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(2 : ℝ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (B : ℝ) (C : ℝ), ¬((B < C) ↔ (True)) :=
  ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {A B C D : ℝ} (hA : A < B) (hB : B < C) (hC : C < D) (hAB : (B - A) / (C - A) = 1 / 5) (hBC : (C - B) / (D - C) = 2 / 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
