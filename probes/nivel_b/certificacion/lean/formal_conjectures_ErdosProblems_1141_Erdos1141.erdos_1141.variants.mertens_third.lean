import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1141

*References:*
- [erdosproblems.com/1141](https://www.erdosproblems.com/1141)
- [A214583](https://oeis.org/A214583)
- [APSSV26b] B. Alexeev, M. Putterman, M. Sawhney, M. Sellke, and G. Valiant,
  [Short proofs in combinatorics, probability and number theory II](https://arxiv.org/abs/2604.06609).
  arXiv:2604.06609 (2026).
- [Or26] Y. Oriike, [Lean formalisation of Erdős problem 1141](https://github.com/yuta0x89/ErdosProblems/blob/a1319f732cdee5140faf47d984e2c451c1184803/Erdos1141.lean) (2026)
- [Po17] P. Pollack, Bounds for the first several prime character nonresidues. Proc. Amer. Math. Soc.
  (2017), 2815--2826.
- [Me1874] F. Mertens, Ein Beitrag zur analytischen Zahlentheorie. J. Reine Angew. Math. (1874),
  46--62.
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for the conference "Paul Erdős
  and his mathematics", Budapest, July 1999 (1999).
-/

section

open Nat Set

namespace Erdos1141

/- ## The two external inputs

The formal proof linked on `erdos_1141` below assumes both of these, and states neither. They are
recorded here so the `assuming` clause on that theorem can name them. -/

/-- The cutoff $m^{1/4 + \varepsilon}$ of Theorem 1.3 of [Po17]. -/
noncomputable def residuePrimeUpperBound (m : ℕ) (ε : ℝ) : ℝ := (m : ℝ) ^ ((1 / 4 : ℝ) + ε)

/--
The primes $\ell \leq m^{1/4+\varepsilon}$ with $\chi(\ell) = 1$.

This does not require $\chi$ to be quadratic. That hypothesis belongs to the theorem below, as it
does in the paper.
-/
noncomputable def residuePrimesUpTo (m : ℕ) (χ : DirichletCharacter ℂ m) (ε : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌈residuePrimeUpperBound m ε⌉₊ + 1)).filter fun ℓ =>
    ℓ.Prime ∧ (ℓ : ℝ) ≤ residuePrimeUpperBound m ε ∧ χ (ℓ : ZMod m) = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 4 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 3)), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n > 3), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 4), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : n ≥ 3), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) < ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (4 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), 1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) →
    (∀ (n : ℕ) (hn : 2 < n), 1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬(1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 / (3 * Real.log n) ≤ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))) ↔ (1 / (3 * Real.log n) ≥ ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
