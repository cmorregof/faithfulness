import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false



set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a ≥ 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a ≥ 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : 1 < a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (1 < a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : 1 < a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : 1 < a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : 1 < a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : 1 < a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (hm : m > 0) (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (hm : m > 0) (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (hm : m > 0) (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (hm : m > 0) (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (hm : m > 0) (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha₀ : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha₀ : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha₀ : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha₀ : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha₀ : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : ¬(a ≤ 1)) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (¬(a ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : ¬(a ≤ 1)) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : ¬(a ≤ 1)) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : ¬(a ≤ 1)) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : ¬(a ≤ 1)) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a ≥ 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} :
    (a > 1) ↔ (a ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : a ≥ 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : a ≥ 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : a ≥ 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) ↔
    (∀ {a m n : ℕ} (ha : a ≥ 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : 1 ≤ a) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (1 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (1 ≤ a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 2) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (hm : m > 0) (hn : n > 0) :
    (a > 1) ↔ (a > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (m > 0) ∧ (n > 0) ∧ (¬((a > 1) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a > 1) ↔ (a > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {a m n : ℕ} (ha : a > 1) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) →
    (∀ {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0), Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ Nat.gcd m n - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hn : n > 0) :
    (m > 0) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (m : ℕ) (n : ℕ), (a > 1) ∧ (n > 0) ∧ (¬((m > 0) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m > 0) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m > 0) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m > 0) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m > 0) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m > 0) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((m > 0) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {a m n : ℕ} (ha : a > 1) (hm : m > 0) (hn : n > 0) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
