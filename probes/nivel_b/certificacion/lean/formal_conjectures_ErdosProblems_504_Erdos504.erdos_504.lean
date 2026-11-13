import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 504

*Reference:* [erdosproblems.com/504](https://www.erdosproblems.com/504)

Blumenthal's minimax angle problem: let $\alpha_N$ be the supremum of all
$0 \le \alpha \le \pi$ such that every set of $N$ points in the plane contains
three distinct points determining an angle at least $\alpha$. Determine
$\alpha_N$.

Szekeres [Sz41] proved $\alpha_{2^n} \le \pi(1 - 1/n)$ together with a lower
bound for $2^n + 1$ points. Erdős and Szekeres [ErSz60] proved
$\alpha_{2^n} = \alpha_{2^n - 1} = \pi(1 - 1/n)$, and Sendov [Se95] determined
$\alpha_N$ for every $N$.

[Sz41] Szekeres, G., _On an extremum problem in the plane_. Amer. J. Math. 63
(1941), 208-210.

[ErSz60] Erdős, P. and Szekeres, G., _On some extremum problems in elementary
geometry_. Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 3-4 (1960-61), 53-62.

[Se95] Sendov, Bl., _Minimax of the angles in a plane configuration of points_.
Acta Math. Hungar. 69 (1995), 27-46. (Reviewed in Zbl 0853.52009, which states the
main theorem as $\alpha_N = \pi\left(1 - \frac{2}{2n+1}\right)$ for
$2^n < N \le 2^n + 2^{n-2}$ and $\alpha_N = \pi\left(1 - \frac{1}{n+1}\right)$ for
$2^n + 2^{n-2} < N \le 2^{n+1}$, $n \ge 2$.)
-/

section

open Real EuclideanGeometry

namespace Erdos504

/--
The minimax angle $\alpha_N$: the supremum of all $\alpha \in [0, \pi]$ such
that every set of $N$ points of the plane contains three pairwise distinct
points $x, z, y$ with $\angle x z y \ge \alpha$ (angle taken at the middle
point $z$).
-/
noncomputable def minimaxAngle (N : ℕ) : ℝ :=
  sSup {α : ℝ | α ∈ Set.Icc 0 π ∧
    ∀ S : Finset ℂ, S.card = N →
      ∃ x ∈ S, ∃ z ∈ S, ∃ y ∈ S, x ≠ z ∧ y ≠ z ∧ x ≠ y ∧
        α ≤ EuclideanGeometry.angle x z y}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 4 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : n ≥ 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn₀ : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n < 3)), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : ¬(n < 3)), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : 2 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : 2 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : 2 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) ↔
    (∀ {n : ℕ} (hn : 2 < n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n > 3), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : n ≥ 4), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
  ∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 2 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) →
    (∀ {n : ℕ} (hn : 3 ≤ n), minimaxAngle (2 ^ n) = (1 - 1 / (n : ℝ)) * π) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
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
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 3 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
