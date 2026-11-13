import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Hadamard's conjecture

*References:*
 - [Wikipedia](https://en.wikipedia.org/wiki/Hadamard_matrix#Hadamard_conjecture)
 - [Tao's optimization constant 23a](https://teorth.github.io/optimizationproblems/constants/23a.html)
 - [Résolution d'une question relative aux déterminants](https://gallica.bnf.fr/ark:/12148/bpt6k486252g/f400.image.r) by *Jacques Hadamard*,  Bull. des sciences math., p.245, 1893
-/

section

namespace Hadamard

/--
A square matrix $M$ with $±1$-entries that satisfies the equality $|M| ≤ n^\frac{n}{2}$ is called a *Hadamard matrix*.
-/
def IsHadamard {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    |M.det| = n ^ ((n : ℝ) / 2)

/--
Equivalently, a square matrix $M$ with $±1$-entries $|A| ≤ n^\frac{n}{2}.$ if it satisfies the equality
$M^TM = n \cdot 1$, where $1$ denotes the unit matrix.
-/
def IsHadamard' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
    (∀ (i j : Fin n), M i j ∈ ({1, -1} : Finset ℝ)) ∧
    M.transpose * M = ↑n

/- Note: the conjecture was originally formulated by
Hadamard as a question: "For which values of $n=4k$ does
a Hadamard matrix exist." However the expectation seems
to be that all such matrices are Hadamard, and the
formalisation has been written with this in mind. -/

/--
The **smallest unsolved order** of the Hadamard conjecture: the smallest $n = 4k$ such that there
is no Hadamard matrix of order $n$, or $\infty$ if there is none.
-/
noncomputable def hadamardConstant : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ¬ ∃ M, IsHadamard (n := 4 * k) M), (4 * k : ℕ∞)

/--
Hadamard constructs a 12 x 12 matrix ...
-/
def H12 : Matrix (Fin 12) (Fin 12) ℝ :=
!![  1,  1,  1,   1,  1,  1,   1,  1,  1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,  -1, -1, -1,   1,  1,  1;
     1,  1,  1,  -1, -1, -1,   1,  1,  1,  -1, -1, -1;
     1, -1, -1,   1, -1, -1,  -1,  1,  1,  -1,  1,  1;
     1, -1, -1,  -1,  1, -1,   1, -1,  1,   1, -1,  1;
     1, -1, -1,  -1, -1,  1,   1,  1, -1,   1,  1, -1;
     1, -1,  1,  -1,  1,  1,  -1,  1, -1,  -1, -1,  1;
     1, -1,  1,   1, -1,  1,  -1, -1,  1,   1, -1, -1;
     1, -1,  1,   1,  1, -1,   1, -1, -1,  -1,  1, -1;
     1,  1, -1,  -1,  1,  1,  -1, -1,  1,  -1,  1, -1;
     1,  1, -1,   1, -1,  1,   1, -1, -1,  -1, -1,  1;
     1,  1, -1,   1,  1, -1,  -1,  1, -1,   1, -1, -1 ]

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  668 < hadamardConstant

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (668 < hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(668 < hadamardConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(668 < hadamardConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (668 < hadamardConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (668 < hadamardConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  669 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (669 ≤ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(669 ≤ hadamardConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(669 ≤ hadamardConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (669 ≤ hadamardConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (669 ≤ hadamardConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≥ hadamardConstant

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (668 ≥ hadamardConstant) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (668 ≥ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(668 ≥ hadamardConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(668 ≥ hadamardConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (668 ≥ hadamardConstant)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (668 ≥ hadamardConstant)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  hadamardConstant ≥ 668

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 668) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (hadamardConstant ≥ 668) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (hadamardConstant ≥ 668) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (hadamardConstant ≥ 668) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (hadamardConstant ≥ 668) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(hadamardConstant < 668)

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (668 ≤ hadamardConstant) ↔ (¬(hadamardConstant < 668)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (¬(hadamardConstant < 668)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (¬(hadamardConstant < 668)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (¬(hadamardConstant < 668)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) ↔
    (¬(hadamardConstant < 668)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  hadamardConstant > 668

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant > 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(hadamardConstant > 668)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(hadamardConstant > 668)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (hadamardConstant > 668)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (hadamardConstant > 668)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  hadamardConstant ≥ 669

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≥ 669) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(hadamardConstant ≥ 669)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(hadamardConstant ≥ 669)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 669)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (hadamardConstant ≥ 669)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  668 ≤ hadamardConstant

set_option maxHeartbeats 200000 in
example : Prop :=
  hadamardConstant ≤ 668

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (hadamardConstant ≤ 668) →
    (668 ≤ hadamardConstant) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (668 ≤ hadamardConstant) →
    (hadamardConstant ≤ 668) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(hadamardConstant ≤ 668)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(hadamardConstant ≤ 668)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (hadamardConstant ≤ 668)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((668 ≤ hadamardConstant) ↔ (hadamardConstant ≤ 668)) :=
  by decide

#eval "FIN_CERTIFICAR"
