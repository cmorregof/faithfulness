import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Algebra.Polynomial.Irreducible
--   import FormalConjecturesForMathlib.Combinatorics.Enumerative.Partition.Basic
/-!
# Parities of partition numbers

There are several conjectures on parities of partition numbers. The most famous conjecture is the
Parkin-Shanks conjecture, which states that the natural density of `n` where the partition number
`p(n)` is even (resp. odd) exists and equals `1/2`.

There are several related (weaker) results toward the conjecture. Kolberg showed that `p(n)` takes
each parity infinitely often. Subbarao conjectured that every arithmetic progression `r (mod t)`
contains infinitely many `n` with `p(n)` even and infinitely many `n` with `p(n)` odd; the even
case was proved by Ono and the odd case by Radu. Quantitative lower bounds for the number of
`n ≤ X` with `p(n)` even (resp. odd) have also been studied. The best known bounds are
`≫ √X log log X` for even values (Bellaïche–Nicolas) and `≫ √X` for odd values (Zheng, in an
appendix to Ono–Swaminathan). Ono–Swaminathan also proved that both parities occur infinitely often
along the quadratic progressions `(D m² + 1) / 24`, and Ono conjectured the same for every nonconstant
integer-valued polynomial that is eventually positive.

*References:*
* [On the distribution of parity in the partition function](https://www.jstor.org/stable/2003251),
  T. R. Parkin, D. Shanks, Math. Comp. 21 (1967), 466–480.
* [Note on the parity of the partition function](https://doi.org/10.7146/math.scand.a-10584),
  O. Kolberg, Math. Scand. 7 (1959), 377–378.
* Some remarks on the partition function, M. V. Subbarao, Amer. Math. Monthly 73 (1966), 851–854.
* [Parity of the partition function in arithmetic progressions](https://doi.org/10.1515/crll.1996.472.1),
  K. Ono, J. Reine Angew. Math. 472 (1996), 1–16.
* [Distribution of parity of the partition function in arithmetic progressions](https://doi.org/10.1016/S0019-3577(99)80014-7),
  S. Ahlgren, Indag. Math. (N.S.) 10 (1999), 173–181.
* [Parity of the partition function](https://doi.org/10.1016/j.aim.2010.02.023), K. Ono,
  Adv. Math. 225 (2010), 349–366.
* [A proof of Subbarao's conjecture](https://doi.org/10.1515/CRELLE.2011.165), C.-S. Radu,
  J. Reine Angew. Math. 672 (2012), 161–175.
* [Parité des coefficients de formes modulaires](https://doi.org/10.1007/s11139-014-9645-9),
  J. Bellaïche, J.-L. Nicolas, Ramanujan J. 40 (2016), 1–44.
* [Nonzero coefficients of half-integral weight modular forms mod ℓ](https://arxiv.org/abs/1704.07440),
  J. Bellaïche, B. Green, K. Soundararajan, Res. Math. Sci. 5 (2018), Paper No. 6.
* [Parity of the partition function in quadratic progressions](https://arxiv.org/abs/2509.09553)
  (with an appendix by Q.-Y. Zheng), K. Ono, A. Swaminathan, arXiv:2509.09553.
* [Cox] D. A. Cox, Primes of the Form $x^2 + ny^2$, 2nd ed., Wiley, 2013.
-/

section

namespace PartitionParity

open Nat Real Filter Topology Asymptotics Polynomial

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (1 ≤ D) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (D > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔ (haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m₁ : ℕ, m₁.Coprime 6 ∧
      m₁ ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m₁ ^ 2 + 1) / 24))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hsq : Squarefree D) (hD : 1 < D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hsq : Squarefree D) (hD : 1 < D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hsq : Squarefree D) (hD : 1 < D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hsq : Squarefree D) (hD : 1 < D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hsq : Squarefree D) (hD : 1 < D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD₀ : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD₀ : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD₀ : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD₀ : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD₀ : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : ¬(D ≤ 1)) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (¬(D ≤ 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : ¬(D ≤ 1)) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : ¬(D ≤ 1)) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : ¬(D ≤ 1)) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : ¬(D ≤ 1)) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (D : ℕ) :
    (1 < D) ↔ (2 ≤ D) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) ↔
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D ≥ 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (D ≥ 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 25 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) :
    (D % 24 = 23) ↔ (D % 25 = 23) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : D > 1) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m < 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (2 < D) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 3 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    (1 < D) ↔ (3 ≤ D) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≤ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) →
    (∀ (D : ℕ) (hD : 2 ≤ D) (hsq : Squarefree D) (h23 : D % 24 = 23), haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=
      ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by lia))⟩
    ∃ m : ℕ, m.Coprime 6 ∧
      m ≥ 12 * NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) + 2 ∧
      Odd (partitionNumber ((D * m ^ 2 + 1) / 24))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (D : ℕ), (1 < D) ∧ (Squarefree D) ∧ (¬((D % 24 = 23) ↔ (D % 25 = 23))) :=
  ⟨(47 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (D : ℕ) (hD : 1 < D) (hsq : Squarefree D) (h23 : D % 24 = 23) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
