import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real Complex Polynomial

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (d > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (hd : d < c) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ₀ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ₀ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ₀ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ₀ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ₀ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : ¬(d ≤ 0)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (¬(d ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : ¬(d ≤ 0)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : ¬(d ≤ 0)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : ¬(d ≤ 0)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : ¬(d ≤ 0)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) :
    (0 < d) ↔ (1 ≤ d) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) ↔
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : d > 0) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d ≤ c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (d ≤ c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (d ≤ c)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 1 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (0 < d) ↔ (1 < d) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (1 < d)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (1 < d)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (1 < d)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (1 < d)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (1 < d)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (d : ℕ), ¬((0 < d) ↔ (1 < d)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 3 * π / 13)) (a b c d : ℕ) (ha : 1 ≤ d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (ζ = exp (I * 2 * π / 13)) ↔ (ζ = exp (I * 3 * π / 13)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) →
    (∀ (ζ : ℂ) (hζ : ζ = exp (I * 2 * π / 13)) (a b c d : ℕ) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3), 1000 * a + 100 * b + 10 * c + d = 7521) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    (d < c) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℕ) (d : ℕ), ¬((d < c) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ζ : ℂ) (a b c d : ℕ) (hζ : ζ = exp (I * 2 * π / 13)) (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a) (h : abs (ζ ^ a + ζ ^ b + ζ ^ c + ζ ^ d) = sqrt 3) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
