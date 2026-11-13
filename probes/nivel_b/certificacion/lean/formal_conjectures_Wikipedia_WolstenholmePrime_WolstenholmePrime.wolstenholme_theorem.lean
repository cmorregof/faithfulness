import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Wolstenholme Prime

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Wolstenholme_prime)
-/

section

namespace WolstenholmePrime

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (p > 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (p > 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (p > 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : 3 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (3 < p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : 3 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : 3 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : 3 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : 3 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (h : p > 3), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (hp : Nat.Prime p) (h : p > 3), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (hp : Nat.Prime p) (h : p > 3), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (hp : Nat.Prime p) (h : p > 3), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (hp : Nat.Prime p) (h : p > 3), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h₀ : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h₀ : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h₀ : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h₀ : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h₀ : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : ¬(p ≤ 3)) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (¬(p ≤ 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : ¬(p ≤ 3)) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : ¬(p ≤ 3)) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : ¬(p ≤ 3)) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : ¬(p ≤ 3)) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (p : ℕ) :
    (p > 3) ↔ (p ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : 3 ≤ p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (3 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (3 ≤ p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (3 ≤ p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : 4 < p) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (hp : Nat.Prime p) :
    (p > 3) ↔ (4 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (Nat.Prime p) ∧ (¬((p > 3) ↔ (4 < p))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬((p > 3) ↔ (4 < p)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (p : ℕ) (h : p > 3) (hp : Nat.Prime p), (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) →
    (∀ (p : ℕ) (h : p ≥ 4) (hp : Nat.Prime p), (3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), (p > 3) ∧ (Nat.Prime p) ∧ (¬((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℕ), ¬(((2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3]) ↔ ((3 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3])) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (p : ℕ) (h : p > 3) (hp : Nat.Prime p) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
