import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Ben Green's Open Problem 21

*References:*
- [Gr24] [Green, Ben. "100 open problems." (2024).](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.21)
- [Ra33] Rado, Richard, *Studien zur Kombinatorik*. Math. Zeit. 36 (1933), 424-480.
- [FoKl06] Fox, Jacob and Kleitman, Daniel, *On Rado's boundedness conjecture*. J. Combin. Theory
  Ser. A 113 (2006), no. 1, 84-100.
- [ElJo23] Ellis, David and Johnson, Robert (editors), *A collection of open problems in
  celebration of Imre Leader's 60th birthday*. arXiv preprint arXiv:2310.18163 (2023).
-/

section

open Finset

namespace Green21

/--
The coefficients $a_1, \dots, a_k$ satisfy **Rado's condition** if $\sum_{i \in I} a_i = 0$ for
some non-empty $I \subseteq [k]$.

For a single homogeneous equation with $k > 0$ nonzero coefficients this is exactly the
criterion of Rado's theorem [Ra33]: $a_1x_1 + \cdots + a_kx_k = 0$ is partition regular if and
only if the coefficients satisfy it. (With a zero coefficient the condition holds trivially, but
e.g. $0 \cdot x_1 + x_2 = 0$ has no solution in positive integers.)
-/
def RadoCondition {k : ℕ} (a : Fin k → ℤ) : Prop :=
  ∃ I : Finset (Fin k), I.Nonempty ∧ ∑ i ∈ I, a i = 0

/--
$c(a_1, \dots, a_k)$, the least number of colours required in order to colour $\mathbb{N}$ so
that there is no monochromatic solution to $a_1x_1 + \cdots + a_kx_k = 0$.

The solutions $x_i$ are required to be *positive*, as in [FoKl06]: were $0$ admitted then
$x_1 = \cdots = x_k = 0$ would be a monochromatic solution for every colouring, and no number of
colours would ever suffice. The $x_i$ are not required to be distinct.

When the coefficients do not satisfy `RadoCondition`, Rado's theorem [Ra33] guarantees that some
finite colouring has no monochromatic solution, so the set below is non-empty and this `sInf` is
a genuine minimum.
-/
noncomputable def minColours {k : ℕ} (a : Fin k → ℤ) : ℕ :=
  sInf {r | ∃ col : ℕ → Fin r, ∀ x : Fin k → ℕ, (∀ i, 0 < x i) →
    (∀ i j, col (x i) = col (x j)) → ∑ i, a i * x i ≠ 0}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a < 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 25) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≥ 24) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≥ minColours a

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  omega

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) :
    (minColours a ≤ 24) ↔ (24 ≥ minColours a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≥ minColours a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≥ minColours a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≥ minColours a) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≥ minColours a) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha₀ : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha₀ : ¬ RadoCondition a), minColours a ≤ 24) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha₀ : ¬ RadoCondition a), minColours a ≤ 24) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha₀ : ¬ RadoCondition a), minColours a ≤ 24) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) ↔
    (∀ (a : Fin 3 → ℤ) (ha₀ : ¬ RadoCondition a), minColours a ≤ 24) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 > minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 25 ≥ minColours a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), minColours a ≤ 24) →
    (∀ (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a), 24 ≤ minColours a) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a : Fin 3 → ℤ) (ha : ¬ RadoCondition a) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
