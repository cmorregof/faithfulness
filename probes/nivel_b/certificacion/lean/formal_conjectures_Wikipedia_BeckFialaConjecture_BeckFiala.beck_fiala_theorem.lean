import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Beck–Fiala theorem and conjecture

Discrepancy of bounded-degree set systems. Given sets $S_1, \dots, S_m \subseteq [n]$
such that every element of $[n]$ belongs to at most $t$ of the sets (the system has
*degree* at most $t$), one seeks a colouring $\chi \colon [n] \to \{-1, +1\}$ making
every set as balanced as possible, i.e. minimizing the *discrepancy*
$\max_i \left|\sum_{j \in S_i} \chi(j)\right|$.

The Beck–Fiala theorem (1981) states that every set system of degree at most $t \ge 1$
has discrepancy at most $2t - 1$. The Beck–Fiala conjecture asserts that the truth is
much stronger: the discrepancy of a degree-$t$ system is $O(\sqrt{t})$, with a constant
independent of $n$, $m$ and $t$.

Despite considerable attention the bound $2t - 1$ has been improved only slightly:
Bukh (2016) proved a bound of the form $2t - \log^* t$ (where $\log^*$ is the iterated
logarithm), and Banaszczyk's vector balancing theorem yields $O(\sqrt{t \log n})$.
The Komlós conjecture (see `KomlosConjecture.lean`) would imply the Beck–Fiala
conjecture, since scaling the incidence vectors of a degree-$t$ system by $1/\sqrt{t}$
produces vectors of Euclidean norm at most $1$.

*References:*
- [Wikipedia](https://en.wikipedia.org/wiki/Beck%E2%80%93Fiala_theorem)
- [J. Beck and T. Fiala, *"Integer-making" theorems*,
  Discrete Applied Mathematics **3** (1981), 1–8](https://doi.org/10.1016/0166-218X(81)90022-6)
- [B. Bukh, *An improvement of the Beck–Fiala theorem*,
  Combinatorics, Probability and Computing **25** (2016), 380–398](https://doi.org/10.1017/S0963548315000140)
- [W. Banaszczyk, *Balancing vectors and Gaussian measures of n-dimensional convex bodies*,
  Random Structures & Algorithms **12** (1998), 351–360](https://doi.org/10.1002/(SICI)1098-2418(199807)12:4%3C351::AID-RSA3%3E3.0.CO;2-S)
-/

section

namespace BeckFiala

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (1 < t) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (t ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔ (∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ₁ : Fin n → ℝ, (∀ j, χ₁ j = 1 ∨ χ₁ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ₁ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht₀ : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht₀ : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht₀ : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht₀ : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht₀ : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : ¬(t < 1)) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (¬(t < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : ¬(t < 1)) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : ¬(t < 1)) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : ¬(t < 1)) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : ¬(t < 1)) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) :
    (1 ≤ t) ↔ (0 < t) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) ↔
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t > 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    (1 ≤ t) ↔ (t > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (t > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (t > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (t > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (t > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (t > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (t > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : t ≥ 1) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n m t : ℕ) (ht : 1 ≤ t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 2 * (t : ℝ) - 1) →
    (∀ (n m t : ℕ) (ht : 0 < t) (S : Fin m → Finset (Fin n)) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t), ∃ χ : Fin n → ℝ, (∀ j, χ j = 1 ∨ χ j = -1) ∧
      ∀ i, |∑ j ∈ S i, χ j| ≤ 3 * (t : ℝ) - 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (ht : 1 ≤ t) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (ht : 1 ≤ t) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (ht : 1 ≤ t) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (ht : 1 ≤ t) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n m t : ℕ) (S : Fin m → Finset (Fin n)) (ht : 1 ≤ t) (hdeg : ∀ j, (Finset.univ.filter fun i => j ∈ S i).card ≤ t) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
