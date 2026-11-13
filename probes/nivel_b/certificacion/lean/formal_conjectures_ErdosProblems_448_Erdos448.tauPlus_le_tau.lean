import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 448

*References:*
- [erdosproblems.com/448](https://www.erdosproblems.com/448)
- [OEIS A397433](https://oeis.org/A397433): the integer sequence $\tau^+(n)$
  (the constant $\alpha$ in Ford's asymptotic is [OEIS A074738](https://oeis.org/A074738)).
- [Er79] Erdős, Paul, Some unconventional problems in number theory. Math. Mag. (1979), 67-70.
- [Er79e] Erdős, Paul, Some unconventional problems in number theory. Astérisque (1979), 73-82.
- [HaTe88] Hall, Richard R. and Tenenbaum, Gérald, Divisors. (1988), xvi+167.
- [ErTe81] Erdős, P., Tenenbaum, G., *Sur la structure de la suite des diviseurs d'un entier.*
  Ann. Inst. Fourier (Grenoble) **31** (1981), 17–37.
- [Fo08] Ford, Kevin, *The distribution of integers with a divisor in a given interval.*
  Ann. of Math. (2) **168** (2008), 367–433.
- [Te13] Tenenbaum, Gérald, *Some of Erdős' unconventional problems in number theory, thirty-four
  years later.* Erdős Centennial, Bolyai Soc. Math. Stud. **25** (2013), 651–681.
-/

section

namespace Erdos448

open Filter Asymptotics Topology

/-- `tauPlus n` (written $\tau^+(n)$) counts the number of $k$ such that $n$ has a divisor in
$[2^k, 2^{k+1})$. Equivalently, the number of distinct values $\lfloor \log_2 d \rfloor$ as $d$
ranges over the divisors of $n$: a divisor $d$ lies in $[2^k, 2^{k+1})$ iff `Nat.log 2 d = k`. -/
def tauPlus (n : ℕ) : ℕ := (n.divisors.image (Nat.log 2)).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n < n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n < n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n < n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n < n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n < n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n < n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n < n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n < n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n < n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n < n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n < n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n < n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n < n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n < n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≥ n.divisors.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), tauPlus n ≥ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n ≥ n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n ≥ n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n ≥ n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n ≥ n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n ≥ n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(tauPlus n ≥ n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n ≥ n.divisors.card)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n ≥ n.divisors.card)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n ≥ n.divisors.card)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n ≥ n.divisors.card)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n ≥ n.divisors.card)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (tauPlus n ≥ n.divisors.card)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), n.divisors.card ≥ tauPlus n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≥ tauPlus n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), n.divisors.card ≥ tauPlus n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), n.divisors.card ≥ tauPlus n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), n.divisors.card ≥ tauPlus n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), n.divisors.card ≥ tauPlus n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), ¬(n.divisors.card < tauPlus n)

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (tauPlus n ≤ n.divisors.card) ↔ (¬(n.divisors.card < tauPlus n)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), ¬(n.divisors.card < tauPlus n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), ¬(n.divisors.card < tauPlus n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), ¬(n.divisors.card < tauPlus n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) ↔
    (∀ (n : ℕ), ¬(n.divisors.card < tauPlus n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), n.divisors.card > tauPlus n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card > tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card > tauPlus n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card > tauPlus n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card > tauPlus n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card > tauPlus n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card > tauPlus n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card > tauPlus n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card > tauPlus n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card > tauPlus n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card > tauPlus n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card > tauPlus n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card > tauPlus n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card > tauPlus n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), tauPlus n ≤ n.divisors.card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ), n.divisors.card ≤ tauPlus n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) →
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ), tauPlus n ≤ n.divisors.card) →
    (∀ (n : ℕ), n.divisors.card ≤ tauPlus n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card ≤ tauPlus n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card ≤ tauPlus n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card ≤ tauPlus n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card ≤ tauPlus n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card ≤ tauPlus n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬(n.divisors.card ≤ tauPlus n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≤ tauPlus n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≤ tauPlus n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≤ tauPlus n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≤ tauPlus n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≤ tauPlus n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((tauPlus n ≤ n.divisors.card) ↔ (n.divisors.card ≤ tauPlus n)) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
