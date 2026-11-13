import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Analysis.Equidistribution.ModOne
--   import FormalConjecturesForMathlib.NumberTheory.NormalNumber
/-!
# Normality of Irrational Algebraic Numbers

It is unknown whether every irrational algebraic real number is normal in any integer base.
Here a real number is *normal in base* $b$ if, for every $k \ge 1$, every string of $k$ digits
appears in its base-$b$ expansion with asymptotic frequency $1/b^k$.
The stronger conjecture that every irrational algebraic real number is absolutely normal is stated
separately: normality in one base and normality in every base are not equivalent definitions.

In a 1950 note on the decimal digits of $\sqrt{2}$, Borel [Bor50] conjectured that every
irrational algebraic number is normal in every base. This was the first publication to address
the expansion of an irrational algebraic number [AB07].

A real number $x$ is normal in base $b$ if and only if the sequence $(b^n x)_{n \ge 0}$ is
uniformly distributed modulo $1$. This was proved by Wall [Wal49]; see also [Bug12, Theorem 4.14]
and [EvdPSW03, p. 127].

*References:*
- [Wikipedia: Normal number](https://en.wikipedia.org/wiki/Normal_number)
- [Bor50] Borel, Émile. "Sur les chiffres décimaux de $\sqrt{2}$ et divers problèmes de
  probabilités en chaîne." C. R. Acad. Sci. Paris 230 (1950): 591-593.
- [AB07] Adamczewski, Boris, and Yann Bugeaud. "On the complexity of algebraic numbers I.
  Expansions in integer bases." Annals of Mathematics 165.2 (2007): 547-565.
- [Wal49] Wall, Donald Dines. "Normal numbers." Ph.D. thesis, University of California, Berkeley,
  1949.
- [Bug12] Bugeaud, Yann. "Distribution modulo one and Diophantine approximation."
  Cambridge Tracts in Mathematics 193. Cambridge University Press, 2012.
- [EvdPSW03] Everest, Graham, Alf van der Poorten, Igor Shparlinski, and Thomas Ward.
  "Recurrence sequences." Mathematical Surveys and Monographs 104. American Mathematical
  Society, Providence, RI, 2003.
- [BC01] Bailey, David H., and Richard E. Crandall. "On the random character of fundamental constant
  expansions." Experimental Mathematics 10.2 (2001): 175-190.
  https://projecteuclid.org/journals/experimental-mathematics/volume-10/issue-2/On-the-random-character-of-fundamental-constant-expansions/em/999188630.full
-/

section

open NormalNumber

namespace AlgebraicNormality

/-- A real number is irrational algebraic if it is algebraic over `ℚ` but not rational. -/
def IsIrrationalAlgebraic (x : ℝ) : Prop :=
  IsAlgebraic ℚ x ∧ Irrational x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (2 < b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : b ≥ 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (b ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : b ≥ 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : b ≥ 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : b ≥ 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : b ≥ 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb₀ : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb₀ : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb₀ : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb₀ : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb₀ : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : ¬(b < 2)) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (¬(b < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : ¬(b < 2)) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : ¬(b < 2)) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : ¬(b < 2)) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : ¬(b < 2)) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 1 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) :
    (2 ≤ b) ↔ (1 < b) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : 1 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : 1 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : 1 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) ↔
    (∀ (b : ℕ) (hb : 1 < b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : b > 2) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (b > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (b > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (b > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (b : ℕ) (hb : 1 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) →
    (∀ (b : ℕ) (hb : 2 ≤ b) (x : ℝ), IsNormalInBase b x ↔ IsEquidistributedModuloOne fun n => (b : ℝ) ^ n * x) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ)  :
    (2 ≤ b) ↔ (1 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), (¬((2 ≤ b) ↔ (1 ≤ b))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (1 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) (hb : 2 ≤ b) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) (hb : 2 ≤ b) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) (hb : 2 ≤ b) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) (hb : 2 ≤ b) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (b : ℕ) (x : ℝ) (hb : 2 ≤ b) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
