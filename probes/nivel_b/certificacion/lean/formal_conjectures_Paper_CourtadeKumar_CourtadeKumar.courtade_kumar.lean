import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Courtade–Kumar (most informative Boolean function) conjecture

Let $X$ be uniform on the Boolean cube $\{0,1\}^n$. Independently of $X$, let the coordinates of $Z$
be i.i.d. Bernoulli random variables with parameter $p \in [0, 1]$, and put $Y = X \oplus Z$,
so that $Y$ is the output of $n$ independent binary symmetric channels with crossover
probability $p$ on input $X$. The **Courtade–Kumar conjecture** asserts that for every
Boolean function $f : \{0,1\}^n \to \{0,1\}$,

  $I(f(X); Y) \le 1 - h(p)$,

where mutual information and binary entropy are measured in bits.

The usual restriction to $p \in [0, 1/2]$ is equivalent to the range used here. For $p > 1/2$,
complementing every output bit replaces $Z$ by its bitwise complement, which is i.i.d.
Bernoulli($1 - p$) noise still independent of $X$; this bijective relabelling of the output
preserves $I(f(X); Y)$, and $h(1 - p) = h(p)$.

This file contains two formulations:

* `CourtadeKumar.courtade_kumar` is the elementary finite-sum statement used by the external
  Lean proof and its comparator check. Its definitions and statement are retained unchanged.
* `CourtadeKumar.variants.courtade_kumar_random_variable` is the random-variable formulation.
  Its product-law hypothesis specifies a uniform input and independent i.i.d. Bernoulli channel
  noise, and its conclusion is about the mutual information of the actual random variables.

`CourtadeKumar.courtade_kumar_iff_random_variable` proves that the two formulations are
equivalent, without using either research statement. Shannon entropy and mutual information of
finite-valued random variables are defined in
`FormalConjecturesForMathlib.InformationTheory.FiniteEntropy`.

For $n \ge 1$, coordinate dictators attain the bound: $I(X_i; Y) = I(X_i; Y_i) = 1 - h(p)$, since
the other output coordinates are independent of $(X_i, Y_i)$. The test `mutualInfo_dictator`
checks $n = 1$.

*References:*
- [CK14] T. A. Courtade and G. R. Kumar, *Which Boolean functions maximize mutual information on
  noisy inputs?*, IEEE Trans. Inf. Theory 60 (2014), no. 8, 4515–4525.

Independent work on the conjecture from September 2026, in alphabetical order:
- [CGJLMNW26] Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff,
  *A Proof of the Most Informative Boolean Function Conjecture*,
  [arXiv:2609.24931](https://arxiv.org/abs/2609.24931). A Lean 4 formalisation of the proof is at
  https://github.com/dpwoodru/general-courtade-kumar-lean.
- [KS26] D. Kramer and M. Saglam, *On the most informative Boolean function under noise*,
  manuscript, https://github.com/deepinfra/courtade-kumar.
- [KT26] Vu Khac Ky and Tuan Tran, *Dictators are most informative*,
  [arXiv:2609.24184](https://arxiv.org/abs/2609.24184). See also their follow-up *Stability of
  the Courtade–Kumar inequality*, [arXiv:2609.31797](https://arxiv.org/abs/2609.31797).
- [MB26] H. Mahdavifar and A. Beirami, *The Most Informative Bit and Beyond: A Proof of the
  Courtade–Kumar Conjecture and Multibit Extensions*,
  [arXiv:2609.26444](https://arxiv.org/abs/2609.26444).
-/

section

namespace CourtadeKumar

open scoped BigOperators ENNReal
open MeasureTheory

/-! ## The elementary formulation

The probability interpretations of `bsc`, `jointProb` and `mutualInfo` assume $0 \le p \le 1$, and
`entropy q` is Shannon entropy when the masses $q$ are nonnegative and sum to one; otherwise these
definitions are just total real-valued expressions. -/

/-- The Boolean cube $\{0,1\}^n$, with bits represented by `Bool`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Binary entropy in bits, $h(p) = -p \log_2 p - (1 - p) \log_2 (1 - p)$, with
$h(0) = h(1) = 0$. -/
noncomputable def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- Transition probability of $n$ independent binary symmetric channels with crossover probability
$p$: $P(Y = y \mid X = x) = \prod_i q_i$, where $q_i = 1 - p$ if $x_i = y_i$ and $q_i = p$
otherwise. -/
noncomputable def bsc {n : ℕ} (p : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if x i = y i then 1 - p else p

/-- The joint probability $P(f(X) = b, Y = y)$ for $X$ uniform on the cube and $Y$ the channel
output on input $X$. -/
noncomputable def jointProb {n : ℕ} (f : Cube n → Bool) (p : ℝ) (b : Bool) (y : Cube n) : ℝ :=
  (2 : ℝ) ^ (-(n : ℤ)) * ∑ x, if f x = b then bsc p x y else 0

/-- Shannon entropy in bits of a probability mass function $q$ on a finite type. -/
noncomputable def entropy {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (q a)) / Real.log 2

/-- The mutual information $I(f(X); Y) = H(f(X)) + H(Y) - H(f(X), Y)$, in bits. -/
noncomputable def mutualInfo {n : ℕ} (f : Cube n → Bool) (p : ℝ) : ℝ :=
  entropy (fun b => ∑ y, jointProb f p b y) + entropy (fun y => ∑ b, jointProb f p b y) -
    entropy (fun z : Bool × Cube n => jointProb f p z.1 z.2)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (p ≥ 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (mutualInfo f p ≤ 1 - binEntropyBits p) ↔ (1 - binEntropyBits p ≥ mutualInfo f p) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀' : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀' : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀' : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀' : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀' : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : ¬(p < 0)) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) :
    (0 ≤ p) ↔ (¬(p < 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : ¬(p < 0)) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : ¬(p < 0)) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : ¬(p < 0)) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) ↔
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : ¬(p < 0)) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p < 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p > 0) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (p > 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (p > 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (p > 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (p > 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (p > 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (p > 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (p > 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (p > 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (p > 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (p > 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (p > 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (p > 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (p > 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : p ≥ 0) (hp₁ : p ≤ 1), mutualInfo f p ≥ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p > mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 < p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≥ mutualInfo f p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₁ : p ≤ 1) :
    (0 ≤ p) ↔ (0 < p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (p ≤ 1) ∧ (¬((0 ≤ p) ↔ (0 < p))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 ≤ p) ↔ (0 < p)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), 1 - binEntropyBits p ≤ mutualInfo f p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p), mutualInfo f p ≤ 1 - binEntropyBits p) →
    (∀ (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1), mutualInfo f p ≤ 1 - binEntropyBits p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) :
    (p ≤ 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (0 ≤ p) ∧ (¬((p ≤ 1) ↔ (True))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (0 ≤ p) ∧ (¬((p ≤ 1) ↔ (True))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (0 ≤ p) ∧ (¬((p ≤ 1) ↔ (True))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (0 ≤ p) ∧ (¬((p ≤ 1) ↔ (True))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (0 ≤ p) ∧ (¬((p ≤ 1) ↔ (True))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), (0 ≤ p) ∧ (¬((p ≤ 1) ↔ (True))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p ≤ 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p ≤ 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p ≤ 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p ≤ 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p ≤ 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p ≤ 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (f : Cube n → Bool) (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
