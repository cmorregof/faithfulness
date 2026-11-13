import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

open Real

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔ (∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i₁ : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i₁ k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn₀ : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n ≤ 0)) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : ¬(n ≤ 0)) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : n > 0) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) > 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (∀ i, 0 < a i) ↔ (∀ i, 0 ≤ a i) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≤ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hq : 0 < q) (hp : 0 < p) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) →
    (∀ {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (S : ℝ) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)), ∀ i : Equiv.Perm (Fin n), ∑ k, (a k^q - a (i k)^q) / (S^p - a k^p) ≥ 0) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (a : Fin n → ℝ) (p q : ℝ) (S : ℝ) (hn : 0 < n) (ha : ∀ i, 0 < a i) (hp : 0 < p) (hq : 0 < q) (hS : S = (∑ i, (a i)^p) ^ ((1 : ℝ) / p)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
