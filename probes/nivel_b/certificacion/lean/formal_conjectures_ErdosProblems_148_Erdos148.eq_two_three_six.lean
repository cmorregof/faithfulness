import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 148

*References:*
- [erdosproblems.com/148](https://www.erdosproblems.com/148)
- [ElPl21] Elsholtz, Christian and Planitzer, Stefan, *Sums of four and more unit fractions and
  approximate parametrizations*. Bull. Lond. Math. Soc. (2021), 695-709.
- [Ko14] Konyagin, S. V., *Double exponential lower bound for the number of representations of
  unity by Egyptian fractions*. Math. Notes (2014), 277-281.
- [OEIS A006585](https://oeis.org/A006585)
-/

section

open Filter Real

namespace Erdos148

/-- `F k` is the number of solutions to $1 = \frac{1}{n_1} + \cdots + \frac{1}{n_k}$ with
$1 \leq n_1 < \cdots < n_k$, that is, the number of $k$-element sets of positive integers whose
reciprocals sum to $1$. -/
noncomputable def F (k : ℕ) : ℕ :=
  {S : Finset ℕ | S.card = k ∧ 0 ∉ S ∧ ∑ n ∈ S, (1 : ℚ) / n = 1}.ncard

/-- The sequence $u_0 = 1$, $u_{n+1} = u_n(u_n + 1)$ of [ElPl21, Corollary 3]:
$1, 2, 6, 42, 1806, \ldots$, a shifted copy of Sylvester's sequence. This is the sequence
`Erdos315.u` of Erdős Problem 315. -/
def u : ℕ → ℕ
  | 0 => 1
  | n + 1 => u n * (u n + 1)

/-- The constant $c_0 = \lim_{n \to \infty} u_n^{2^{-n}} = 1.5979102\ldots$ of
[ElPl21, Corollary 3]. The sequence $u_n^{2^{-n}}$ is increasing and bounded by $2$
[ElPl21, Remark 3], so the limit is its supremum. This constant is the square of the Vardi
constant $1.26408\ldots$, which is `Erdos315.c₀`. -/
noncomputable def c₀ : ℝ := ⨆ n : ℕ, (u n : ℝ) ^ ((1 : ℝ) / 2 ^ n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(4 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (x > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hxy : x < y) (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hxy : x < y) (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hxy : x < y) (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hxy : x < y) (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hxy : x < y) (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx₀ : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx₀ : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx₀ : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx₀ : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx₀ : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : ¬(x ≤ 0)) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (¬(x ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : ¬(x ≤ 0)) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : ¬(x ≤ 0)) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : ¬(x ≤ 0)) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : ¬(x ≤ 0)) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} :
    (0 < x) ↔ (1 ≤ x) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) ↔
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : x > 0) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(4 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (x ≤ y) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (x ≤ y))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (x ≤ y)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (0 < x) ↔ (1 < x) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((0 < x) ↔ (1 < x))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ), ¬((0 < x) ↔ (1 < x)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 1 ≤ x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 3 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(0 : ℕ), (4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (x < y) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬(x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(4 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (2 : ℕ), (6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(2 : ℕ), (6 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(1 : ℕ), (4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), ¬((x = 2 ∧ y = 3 ∧ z = 6) ↔ (x = 3 ∧ y = 3 ∧ z = 6)) :=
  ⟨(3 : ℕ), (3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) →
    (∀ {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1), x = 2 ∧ y = 3 ∧ z = 6) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    (x < y) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ) (z : ℕ), (0 < x) ∧ (y < z) ∧ ((1 : ℚ) / x + 1 / y + 1 / z = 1) ∧ (¬((x < y) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (x : ℕ) (y : ℕ), ¬((x < y) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {x y z : ℕ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) (h : (1 : ℚ) / x + 1 / y + 1 / z = 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
