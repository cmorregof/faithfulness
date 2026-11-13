import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Indicator sequence for 5 Fibonacci numbers with n digits

$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
For the partial sums $S(n) = \sum_{k=1}^n a(k)$, it is conjectured that
$\beta-2 < S(n)-\alpha n < \beta-1$, where $\alpha = \log(10)/\log(\phi) - 4$
and $\beta = \log(5)/(2\log(\phi)) - 1$.

*References:*
- [A105565](https://oeis.org/A105565)
-/

section

namespace OeisA105565

open Nat Finset Real

/--
The primary defining sequence `a`.
$a(n) = 1$ if exactly 5 Fibonacci numbers exist with exactly $n$ digits, otherwise $0$.
That is, $a(n) = 1$ if the number of indices $k \in \mathbb{N}$ such that
$10^{n-1} \le \mathrm{fib}(k) < 10^n$ is 5.
-/
def a (n : ℕ) : ℕ :=
  if n > 0 then
    -- $n$ is the number of digits, so $n \ge 1$.
    let lowerBound : ℕ := 10 ^ (n - 1)
    let upperBound : ℕ := 10 ^ n

    -- A safe upper bound for the index $k$.
    let maxK : ℕ := 5 * n + 10

    -- Count indices $k$ in range $[0, maxK)$ such that $\mathrm{fib}(k)$ has $n$ digits.
    let count : ℕ :=
      (filter (fun k => lowerBound ≤ Nat.fib k ∧ Nat.fib k < upperBound) (range maxK)).card

    if count = 5 then 1 else 0
  else
    0

/-- The golden ratio $\phi = (1 + \sqrt{5})/2$. -/
noncomputable def phi : Real := goldenRatio

/-- The constant $\alpha = \log(10)/\log(\phi) - 4$. -/
noncomputable def alphaConst : Real := Real.log 10 / Real.log phi - 4

/-- The constant $\beta = \log(5)/(2\log(\phi)) - 1$. -/
noncomputable def betaConst : Real := Real.log 5 / (2 * Real.log phi) - 1

/-- The partial sum $S(n) = \sum_{k=1}^n a(k)$. -/
noncomputable def s (n : ℕ) : Real :=
  (Finset.Icc 1 n).sum (fun k => (a k : Real))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 2 < s n - alphaConst * (n : Real))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 2 < s n - alphaConst * (n : Real))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 2 < s n - alphaConst * (n : Real))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 2 < s n - alphaConst * (n : Real))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 2 < s n - alphaConst * (n : Real))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 2 < s n - alphaConst * (n : Real))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1 ∧ betaConst - 2 < s n - alphaConst * (n : Real)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn₀ : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 1)), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : ¬(n < 1)), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n > 1), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (1 ≤ n) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : n ≥ 1), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 0 < n), betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (betaConst - 3 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) →
    (∀ (n : ℕ) (hn : 1 ≤ n), s n - alphaConst * (n : Real) < betaConst - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((betaConst - 2 < s n - alphaConst * (n : Real) ∧
      s n - alphaConst * (n : Real) < betaConst - 1) ↔ (s n - alphaConst * (n : Real) < betaConst - 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 1 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
