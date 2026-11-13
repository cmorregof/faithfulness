import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 261

*References:*
 - [erdosproblems.com/261](https://www.erdosproblems.com/261)
 - [BoLo90] Borwein, Peter and Loring, Terry A., Some questions of Erdős and Graham on numbers
    of the form $\sum g_n/2^{g_n}$. Math. Comp. (1990), 377--394.
 - [Er88c] Erdős, P., On the irrationality of certain series: problems and results. New advances
    in transcendence theory (Durham, 1986) (1988), 102--109.
 - [TUZ20] Tengely, Szabolcs and Ulas, Maciej and Zygadlo, Jakub, On a Diophantine equation of
    Erdős and Graham. J. Number Theory (2020), 445--459.
 - [PALOMAR-2026-10-11-000016](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-11-000016&version=1)
-/

section

open scoped Cardinal

namespace Erdos261

/-- A natural number $n$ is said to have property `Erdos261Prop` if there exist $t \ge 2$
pairwise distinct positive integers $a_1, \ldots, a_t$ such that
$n / 2^n = \sum_{1 \le k \le t} a_k / 2^{a_k}$. -/
def Erdos261Prop (n : ℕ) : Prop := ∃ᵉ (t ≥ 2) (a : Fin t → ℕ), a.Injective ∧
  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)

/-- A canonical infinite representation of a rational number $x$ by positive integers. The
denominators are strictly increasing so that reorderings are not counted as different
representations. -/
def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m > 0), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : m > 0), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : m > 0), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : m > 0), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : m > 0), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm₀ : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm₀ : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm₀ : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm₀ : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm₀ : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : ¬(m ≤ 0)), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : ¬(m ≤ 0)), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : ¬(m ≤ 0)), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : ¬(m ≤ 0)), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : ¬(m ≤ 0)), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : m > 0), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ)  :
    (0 < m) ↔ (1 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((0 < m) ↔ (1 < m))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬((0 < m) ↔ (1 < m))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ) (hm : 0 < m), let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) →
    (∀ (m : ℕ) (hm : 1 ≤ m), let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (0 < m) ∧ (¬(let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((let n := 2 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ)) ↔ (let n := 3 ^ (m + 1) - m - 2
    n / (2 ^ n : ℚ) = ∑ k ∈ Finset.Ioc n (n + m), k / (2 ^ k : ℚ))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 0 < m) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 0 < m) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 0 < m) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 0 < m) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (m : ℕ) (hm : 0 < m) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
