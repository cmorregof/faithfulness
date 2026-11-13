import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1204

*References:*
- [erdosproblems.com/1204](https://www.erdosproblems.com/1204)
- [El65] Elliott, P. D. T. A., *On sequences of integers*. Quart. J. Math. Oxford Ser. (2) 16
  (1965), 35-45.
- [Er80] Erdős, P., *A survey of problems in combinatorial number theory*. Ann. Discrete Math. 6
  (1980), 89-115.
- [Po14c] Polymath, D. H. J., *Variants of the Selberg sieve, and bounded intervals containing
  many primes*. Res. Math. Sci. 1 (2014), Art. 12.
  [arXiv:1407.4897](https://arxiv.org/abs/1407.4897)
-/

section

open Filter Asymptotics

namespace Erdos1204

/-- A finite set `S` of natural numbers is *admissible* if it misses at least one residue class
modulo every prime. A sequence $0\leq a_1<\cdots <a_k$ is identified with the set of its values. -/
def IsAdmissible (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ S, (a : ZMod p) ≠ r

/-- $A(k)$: the least possible value of $a_k$ over admissible sequences $0\leq a_1<\cdots <a_k$.
Any $k$ primes larger than $k$ form an admissible set, so `sInf` is a true minimum. -/
noncomputable def A (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∀ a ∈ S, a ≤ m}

/-- The least possible value of $a_1+\cdots+a_k$ over admissible sequences
$0\leq a_1<\cdots <a_k$. As for `A`, the minimum exists. -/
noncomputable def minSum (k : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ S : Finset ℕ, S.card = k ∧ IsAdmissible S ∧ ∑ a ∈ S, a = s}

/-- $B(k)=\min \frac{a_1+\cdots+a_k}{k}$. -/
noncomputable def B (k : ℕ) : ℝ := (minSum k : ℝ) / k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k < m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), A k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (A k ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≥ A k

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (m ≥ A k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≥ A k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≥ A k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≥ A k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≥ A k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hadm : IsAdmissible S) (hS : S.card = k) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hadm : IsAdmissible S) (hS : S.card = k) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hadm : IsAdmissible S) (hS : S.card = k) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hadm : IsAdmissible S) (hS : S.card = k) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hadm : IsAdmissible S) (hS : S.card = k) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS₀ : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS₀ : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS₀ : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS₀ : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS₀ : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), ¬(m < A k)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} :
    (A k ≤ m) ↔ (¬(m < A k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), ¬(m < A k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), ¬(m < A k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), ¬(m < A k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) ↔
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), ¬(m < A k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m > A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m > A k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a < m), m ≥ A k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) :
    (∀ a ∈ S, a ≤ m) ↔ (∀ a ∈ S, a < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), A k ≤ m) →
    (∀ {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m), m ≤ A k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((A k ≤ m) ↔ (m ≤ A k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} {S : Finset ℕ} (hS : S.card = k) (hadm : IsAdmissible S) (hm : ∀ a ∈ S, a ≤ m) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
