import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1026

*References:*
- [erdosproblems.com/1026](https://www.erdosproblems.com/1026)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Ha57] Hanani, Haim, *On the number of monotonic subsequences*. Bull. Res. Council Israel
  Sect. F (1957/58), 11-13.
- [St95] Steele, J. Michael, *Variations on the monotone subsequence theme of Erdős and
  Szekeres*. (1995), 111-131.
- [TWY16] Tidor, J. and Wang, V. and Yang, B., *$1$-color avoiding paths, special tournaments,
  and incidence geometry*. arXiv:1608.04153 (2016).
- [Wa17] Wagner, Adam Zsolt, *Large subgraphs in rainbow-triangle free colorings*. J. Graph
  Theory (2017), 141-148.
-/

section

namespace Erdos1026

open Filter

/--
The set of sums $\sum x_{i_r}$, where $x_{i_1},\ldots,x_{i_r}$ ranges over the monotonic
subsequences of the sequence $x_1,\ldots,x_n$.
-/
def monotonicSubsequenceSums {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  {S | ∃ I : Finset (Fin n), (MonotoneOn x ↑I ∨ AntitoneOn x ↑I) ∧ (∑ i ∈ I, x i) = S}

/--
The set of constants $c$ such that, for all sequences of $n$ distinct positive real numbers
$x_1,\ldots,x_n$,
$$
\max\left(\sum x_{i_r}\right) > (c-o(1))\frac{1}{\sqrt{n}}\sum x_i
$$
(where the maximum is taken over all monotonic subsequences).

The source reduces to positive sequences. With signed sequences the condition is not a vanishing
error term: for $\varepsilon > |c|$ and $x_i = -i$ the right-hand side is positive while every
subsequence sum is nonpositive, so no constant would be admissible.
-/
def admissibleConstants : Set ℝ :=
  {c : ℝ | ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → ℝ, Function.Injective x →
    (∀ i, 0 < x i) →
    ∃ S ∈ monotonicSubsequenceSums x, (c - ε) / Real.sqrt (n : ℝ) * (∑ i, x i) ≤ S}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔ (∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S₁ ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S₁) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk₀ : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k ≤ 0)) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : ¬(k ≤ 0)) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) ↔
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : k > 0) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) < S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 ≤ x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1) :
    (∀ i, 0 < x i) ↔ (∀ i, 0 ≤ x i) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 1 ≤ k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≥ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx' : ∀ i, 0 < x i) (hx : Function.Injective x) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) →
    (∀ (k : ℕ) (hk : 0 < k) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1), ∃ S ∈ monotonicSubsequenceSums x, 1 / (k : ℝ) ≤ S) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    (0 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (x : Fin (k ^ 2) → ℝ) (hk : 0 < k) (hx : Function.Injective x) (hx' : ∀ i, 0 < x i) (hsum : (∑ i, x i) = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
