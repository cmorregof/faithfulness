import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Optimal monotone families for the discrete isoperimetric inequality

*References:*
- [mathoverflow/10799](https://mathoverflow.net/questions/10799)
  asked by user [*Gil Kalai*](https://mathoverflow.net/users/1532/gil-kalai)
- [Optimal Monotone Families for the Discrete Isoperimetric Inequality](https://gilkalai.wordpress.com/ai/optimal-monotone-families-for-the-discrete-isoperimetric-inequality/)
  by *Gil Kalai* (2026), a Polymath project with AI agents
- [An Isoperimetric Inequality for the Hamming Cube and Integrality Gaps in Bounded-Degree
  Graphs](https://arxiv.org/abs/math/0603218) by *Jeff Kahn* and *Gil Kalai* (2006)
- [A Proof of the Kahn–Kalai Conjecture](https://arxiv.org/abs/2203.17207) by *Jinyoung Park*
  and *Huy Tuan Pham* (2022)

-/

section

namespace Mathoverflow10799

open Finset Real

/--
Start with a set $X=\{1,2,...,n\}$ of $n$ elements and the family $2^X$ of all subsets of $X$.
For a real number $p$ between zero and one, we consider a probability distribution $\mu_p$ on
$2^X$ where the probability that $i \in S$ is $p$, independently for different $i$'s.
Thus for $p=1/2$ we get the uniform probability distribution.

For $S \subseteq \{0, \ldots, n-1\}$, its probability is $p^{|S|} (1-p)^{n - |S|}$.
-/
noncomputable def μ {n : ℕ} (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  p ^ #S * (1 - p) ^ (n - #S)

/--
The $p$-biased measure of a family $\mathcal F \subseteq 2^{[n]}$,
i.e. $\mu_p(\mathcal F) = \sum_{S \in \mathcal F} \mu_p(S)$.
-/
noncomputable def μFamily {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S ∈ F, μ p S

/--
Given a family $F$, for a subset $S$ of $X$, we write $h(S)$ as the number of subsets $T$ in $X$
such that
(1) $T$ differs from $S$ in exactly one element
(2) Exactly one set among $S$ and $T$ belongs to $F$.
-/
def boundaryCount (n : ℕ) (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ Xor (S ∈ F) (symmDiff S {i} ∈ F)).card

/--
The edge-boundary of $F$ is the expectation of $h(S)$ (according to $\mu_p$) over all
subsets $S$ of $X$. It is denoted by $I^p(F)$.
-/
noncomputable def edgeBoundary (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) : ℝ :=
  ∑ S : Finset (Fin n), μ p S * boundaryCount n F S

/--
A family $F$ of subsets of $2^X$ is monotone increasing if when $S$ belongs to $F$ and $T$
contains $S$ then $T$ also belongs to $F$. (Monotone increasing families also also called "filtes"
and "up-families".) From now on we will restrict our attention to the case of monotone increasing
families.

This is Mathlib's `IsUpperSet` applied to the coercion of $\mathcal F$ to a set,
using the fact that `≤` on `Finset` is `⊆`.
-/
abbrev IsMonotoneIncreasing {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  IsUpperSet (↑F : Set (Finset (Fin n)))

/--
We say that a family is optimal for $\mu_p$ if the isoperimetric inequality (IR) is sharp up to a
multiplicative constant $1000 \log (1/p)$.

Since the lower bound from (IR) is
$$\frac{\mu_p(\mathcal F) \cdot \log(1/\mu_p(\mathcal F))}{p \cdot \log(1/p)},$$
multiplying by $1000 \log(1/p)$ gives the condition
$$I^p(\mathcal F) \le \frac{1000}{p} \cdot \mu_p(\mathcal F) \cdot \log \frac{1}{\mu_p(\mathcal F)}.$$
-/
noncomputable def IsOptimal {n : ℕ} (p : ℝ) (F : Finset (Finset (Fin n))) : Prop :=
  let m := μFamily p F
  edgeBoundary n p F ≤ 1000 * Real.log (1 / p) * (m * Real.logb p m / p)

/--
Following Kahn–Kalai, a family is $(C \log(1/p), p)$-optimal if the isoperimetric inequality
(IR) is sharp up to the multiplicative constant $C \log(1/p)$, i.e.
$$I^p(\mathcal F) \le \frac{C}{p} \cdot \mu_p(\mathcal F) \cdot \log \frac{1}{\mu_p(\mathcal F)}.$$
`IsOptimal` is the special case $C = 1000$.
-/
noncomputable def IsOptimalWith {n : ℕ} (C p : ℝ) (F : Finset (Finset (Fin n))) : Prop :=
  let m := μFamily p F
  edgeBoundary n p F ≤ C * Real.log (1 / p) * (m * Real.logb p m / p)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (0 ≤ p) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (0 ≤ p)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (0 ≤ p)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (0 ≤ p)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (0 ≤ p)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (0 ≤ p)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (0 ≤ p)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : p > 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (p > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : p > 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : p > 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : p > 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : p > 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp' : p < 1) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp₀ : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp₀ : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp₀ : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp₀ : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp₀ : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : ¬(p ≤ 0)) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) :
    (0 < p) ↔ (¬(p ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : ¬(p ≤ 0)) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : ¬(p ≤ 0)) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : ¬(p ≤ 0)) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) ↔
    (∀ (n : ℕ) (p : ℝ) (hp : ¬(p ≤ 0)) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : p ≥ 0) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    (0 < p) ↔ (p ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (p ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (p ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (p ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (p ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (p ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((0 < p) ↔ (p ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) →
    (∀ (n : ℕ) (p : ℝ) (hp : 0 < p) (hp' : p < 1) (F : Finset (Finset (Fin n))) (hF : IsMonotoneIncreasing F), let m := μFamily p F
    edgeBoundary n p F ≥ m * Real.logb p m / p) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hF : IsMonotoneIncreasing F) :
    (p < 1) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p < 1) ↔ (True)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p < 1) ↔ (True)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p < 1) ↔ (True)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p < 1) ↔ (True)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p < 1) ↔ (True)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (p : ℝ), ¬((p < 1) ↔ (True)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (p : ℝ) (F : Finset (Finset (Fin n))) (hp : 0 < p) (hp' : p < 1) (hF : IsMonotoneIncreasing F) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
