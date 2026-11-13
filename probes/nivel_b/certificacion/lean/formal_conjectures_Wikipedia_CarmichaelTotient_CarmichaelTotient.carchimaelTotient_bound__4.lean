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
  ∀ {n : ℕ} (hn' : n < 10 ^ (10 ^ 10)) (hn : 0 < n), CarmichaelTotientFor n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) ↔
    (∀ {n : ℕ} (hn' : n < 10 ^ (10 ^ 10)) (hn : 0 < n), CarmichaelTotientFor n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) ↔
    (∀ {n : ℕ} (hn' : n < 10 ^ (10 ^ 10)) (hn : 0 < n), CarmichaelTotientFor n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) ↔
    (∀ {n : ℕ} (hn' : n < 10 ^ (10 ^ 10)) (hn : 0 < n), CarmichaelTotientFor n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n) (hn' : n < 10 ^ (10 ^ 10)), CarmichaelTotientFor n) ↔
    (∀ {n : ℕ} (hn' : n < 10 ^ (10 ^ 10)) (hn : 0 < n), CarmichaelTotientFor n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

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
