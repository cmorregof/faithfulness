import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Lesser of twin primes

Primes $p$ such that $p+2$ is also prime.

*References:*
- [A001359](https://oeis.org/A001359)
-/

section

namespace OeisA1359

/-- The $n$-th lesser twin prime, with $a(0) = 0$. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n > 0 then
    Nat.nth (fun p => p.Prime ∧ (p + 2).Prime) (n - 1)
  else
    0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k ≥ 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(991 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(990 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(992 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(991 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(990 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(992 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (1 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk₀ : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk₀ : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk₀ : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk₀ : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k ≤ 1)), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (¬(k ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 1)), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 1)), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 1)), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 1)), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (k > 1) ↔ (k ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔
    (∀ (k : ℕ) (hk : k ≥ 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (1 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (1 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (1 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (1 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (1 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (1 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (1 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (1 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (1 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (1 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (1 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (1 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (1 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : 1 < k), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(991 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(990 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(992 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (k > 1) ∧ (¬(let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(991 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(990 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(992 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) ↔ (let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 3).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ])))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k > 2), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 1), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) →
    (∀ (k : ℕ) (hk : k ≥ 3), let Pk := Nat.nth Nat.Prime (k - 1)
    let Pk_succ := Nat.nth Nat.Prime k
    let Congruence := Pk.factorial ≡ 1 [MOD Pk_succ]
    let IsLesserTwinPrime := (Pk + 2).Prime
    let Wk_prod : ℕ := ∏ i ∈ Finset.Icc (Pk + 1) (Pk_succ - 2), i
    Congruence ↔ (IsLesserTwinPrime ∨ (k = 991) ∨ (Pk_succ - Pk > 2 ∧ Wk_prod ≡ 1 [MOD Pk_succ]))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (k > 1) ↔ (k ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((k > 1) ↔ (k ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k > 1) ↔ (k ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k > 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k > 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k > 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k > 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : k > 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
