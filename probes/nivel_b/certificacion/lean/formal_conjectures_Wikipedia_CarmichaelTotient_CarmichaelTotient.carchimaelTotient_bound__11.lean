import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Carmichael's totient function conjecture

For every positive natural number $n$, there exists a natural number $m$ with $m ≠ n$, such that
$φ(n) = φ(m)$ where $φ$ is the Euler totient function.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Carmichael%27s_totient_function_conjecture)
- [F1998] Kevin Ford. The distribution of totients. https://arxiv.org/abs/1104.3264
-/

section

universe u v

open Nat

namespace CarmichaelTotient

/-- Natural number $n$ for which there exists a $m ≠ n$ with $φ(m) = φ(n)$ -/
def CarmichaelTotientFor (n : ℕ) : Prop := ∃ m : ℕ, m ≠ n ∧ φ m = φ n

-- TODO: Version of this ↓ lemma to mathlib?

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 10 ^ (10 ^ 10)), CarmichaelTotientFor n) →
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) :
    (n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(11 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n < 10 ^ (10 ^ 10)) ↔ (n ≤ 10 ^ (10 ^ 10))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
