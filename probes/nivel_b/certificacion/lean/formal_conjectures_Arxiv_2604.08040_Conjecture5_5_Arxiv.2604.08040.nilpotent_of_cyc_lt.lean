import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Group structure via subgroup counts

*Reference:* [arXiv:2604.08040v1](https://arxiv.org/abs/2604.08040v1)
**Group Structure via Subgroup Counts**
by *Angsuman Das, Hiranya Kishore Dey, Khyati Sharma* (2026)

For a finite group $G$, let $\mathrm{cyc}(G)$ denote the number of cyclic subgroups of $G$,
and let $t = \pi(G)$ denote the number of distinct prime divisors of $|G|$.

The paper establishes several structural results of the form
"if $\mathrm{cyc}(G)$ or $\mathrm{sub}(G)$ is small relative to $2^t$, then $G$
has a strong structural property":

* $\mathrm{cyc}(G) < 5 \cdot 2^{t-2} \implies G$ is nilpotent (Theorem 3.1)
* $\mathrm{cyc}(G) < 2^{t+1} \implies G$ is supersolvable (Theorem 4.2)
* $\mathrm{sub}(G) < 59 \cdot 2^{t-3} \implies G$ is solvable (Theorem 5.3)

**Conjecture 5.5** proposes the analogue for solvability via cyclic subgroup count:
if $\mathrm{cyc}(G) < 2^{t+2}$, then $G$ is solvable.

* **In-Paper Location:** Conjecture 5.5, Section 5 "Solvability of a group from $\mathrm{sub}(G)$"
  ([PDF page 15](https://arxiv.org/pdf/2604.08040v1#page=15))
* **OpenConjecture ID:** 1512
-/

section

namespace Arxiv.«2604.08040»

variable (G : Type*) [Group G] [Fintype G]

/--
The number of cyclic subgroups of a finite group `G`.
-/
noncomputable def cyc : ℕ :=
  Nat.card {H : Subgroup G // IsCyclic H}

/--
The number of distinct prime divisors of the order of `G`.

This is $\pi(G)$ in the notation of the paper.
-/
noncomputable def numPrimeFactors : ℕ :=
  (Fintype.card G).primeFactors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : cyc G < 6 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  omega

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  simp_all

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)) := by
  plausible

set_option maxHeartbeats 200000 in
example : (¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2)))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (cyc G < 6 * 2 ^ (numPrimeFactors G - 2))) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : 5 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (5 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : 5 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : 5 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : 5 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : 5 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h₀ : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h₀ : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h₀ : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h₀ : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h₀ : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : ¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : ¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)), Group.IsNilpotent G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : ¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)), Group.IsNilpotent G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : ¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)), Group.IsNilpotent G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) ↔
    (∀ (h : ¬(5 * 2 ^ (numPrimeFactors G - 2) ≤ cyc G)), Group.IsNilpotent G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) →
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)), Group.IsNilpotent G) →
    (∀ (h : 6 * 2 ^ (numPrimeFactors G - 2) > cyc G), Group.IsNilpotent G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  omega

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  simp_all

set_option maxHeartbeats 200000 in
example   :
    (cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G) := by
  plausible

set_option maxHeartbeats 200000 in
example : (¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) ↔ (6 * 2 ^ (numPrimeFactors G - 2) > cyc G)) :=
  by decide

set_option maxHeartbeats 200000 in
example  (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example  (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example  (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example  (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example  (h : cyc G < 5 * 2 ^ (numPrimeFactors G - 2)) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
