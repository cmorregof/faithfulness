import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Strong Sensitivity Conjecture (`bs(f) ≤ s(f)^2`)

This file formalizes the *strong* sensitivity conjecture, asserting:

For every Boolean function `f : {0,1}^n → {0,1}`,
`bs(f) ≤ s(f)^2`,
where bs(f) denotes block sensitivity and s(f) denotes sensitivity.

Huang's theorem proves a *quartic* upper bound, `bs(f) ≤ s(f)^4`, thereby
resolving the most widely known form of the sensitivity conjecture.

We now ask whether a stronger upper bound holds. Interestingly, the original
paper of Nisan and Szegedy, where the sensitivity conjecture first appeared,
already speculated that a *quadratic* upper bound might be the correct
relation. On the lower bound side, Rubinstein
(https://link.springer.com/article/10.1007/BF01200762) constructed Boolean functions
exhibiting the first quadratic separation. The best gap known before [OAI26],
due to Ambainis and Sun (https://arxiv.org/abs/1108.3494), was
`bs(f) ≥ (2/3)⋅s(f)^2`.

In September 2026 an internal OpenAI model disproved the quadratic bound [OAI26]: it
constructs total Boolean functions with `bs(f) / s(f)^2` arbitrarily large.

*References:*
* [OAI26] [A superquadratic separation between sensitivity and block sensitivity](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-superquadratic-separation-between-sensitivity-and-block-sensitivity-September-25-2026/paper.pdf)
  by OpenAI, OpenAI Math Release preprint (2026)
* [Induced Subgraphs of Hypercubes and a Proof of the Sensitivity Conjecture](https://arxiv.org/abs/1907.00847)
  by Hao Huang (see Section 3, Concluding Remarks)
* [Variations on the Sensitivity Conjecture](https://arxiv.org/abs/1011.0354)
  by Pooya Hatami, Raghav Kulkarni, and Denis Pankratov (see Question 3.1)
* [On the Degree of Boolean Functions as Real Polynomials](https://link.springer.com/article/10.1007/BF01263419)
  by Noam Nisan, and Mario Szegedy (see Section 4, Open Problems)
-/

section

namespace StrongSensitivityConjecture

open Finset Function

section Sensitivity

variable {n : ℕ}

/-- Flip operator,
`flip x B` returns input `x` with bits in block `B` inverted. -/
def flip (x : Fin n → Bool) (B : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ B then !(x i) else x i

/-- Local sensitivity s(f,x),
number of indices where flipping one bit changes the value of `f`. -/
def sensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  #{i | f (flip x {i}) ≠ f x}

/-- Global sensitivity s(f),
maximum sensitivity of `f` over all inputs. -/
def sensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (sensitivityAt f)

/-- Check validity of block collection (disjoint and sensitive),
A collection of blocks `cB` is valid for `f` at `x` if the blocks are
disjoint and flipping any block changes `f(x)`. -/
def IsValidBlockConfig (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (cB : Finset (Finset (Fin n))) : Prop :=
  (cB : Set (Finset (Fin n))).PairwiseDisjoint id ∧
  ∀ B ∈ cB, f (flip x B) ≠ f x

/-- Local block sensitivity bs(f,x),
maximum size of a collection of sensitive, disjoint blocks for `f` at `x`. -/
noncomputable def blockSensitivityAt (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  open scoped Classical in
  Finset.sup {cB | IsValidBlockConfig f x cB} card

/-- Global block sensitivity of `f`,
maximum block sensitivity of `f` over all inputs. -/
noncomputable def blockSensitivity (f : (Fin n → Bool) → Bool) : ℕ :=
  univ.sup (blockSensitivityAt f)

/-- Simple test example.
For multiples of four with $n \ge 12$, this Boolean function has block sensitivity
strictly greater than its sensitivity. Source:
[Nisan1989](https://dl.acm.org/doi/10.1145/73007.73038).

`nisanExample(x) = 1` iff the Hamming weight of $x$ is either
$n/2$ or $n/2 + 1$.
The function is symmetric, so its value only depends on the Hamming weight
of the input. -/
def nisanExample (n : ℕ) (x : Fin n → Bool) : Bool :=
  let w := #{i | x i}
  decide ((w : ℚ) ∈ ({(n / 2 : ℚ), (n / 2 : ℚ) + 1} : Finset ℚ))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

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
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn_pos : 0 < n) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn_pos : 0 < n) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn_pos : 0 < n) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn_pos : 0 < n) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn_pos : 0 < n) (hn : 4 ∣ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn₀ : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn₀ : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn₀ : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn₀ : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : ¬(n ≤ 0)), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : ¬(n ≤ 0)), sensitivity (nisanExample n) = n / 2 + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : ¬(n ≤ 0)), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : ¬(n ≤ 0)), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : ¬(n ≤ 0)), sensitivity (nisanExample n) = n / 2 + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) ↔
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : n > 0), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 1 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (4 ∣ n) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

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
  ∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n), sensitivity (nisanExample n) = n / 2 + 2) →
    (∀ (n : ℕ) (hn : 5 ∣ n) (hn_pos : 1 ≤ n), sensitivity (nisanExample n) = n / 2 + 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn_pos : 0 < n) :
    (4 ∣ n) ↔ (5 ∣ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((4 ∣ n) ↔ (5 ∣ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((4 ∣ n) ↔ (5 ∣ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 4 ∣ n) (hn_pos : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
