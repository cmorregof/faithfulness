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
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10000), Erdos261Prop n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10000), Erdos261Prop n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≤ 10000) (hn_pos : 0 < n), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn : n ≤ 10000) (hn_pos : 0 < n), Erdos261Prop n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn : n ≤ 10000) (hn_pos : 0 < n), Erdos261Prop n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn : n ≤ 10000) (hn_pos : 0 < n), Erdos261Prop n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn : n ≤ 10000) (hn_pos : 0 < n), Erdos261Prop n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos₀ : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos₀ : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos₀ : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos₀ : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos₀ : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : ¬(n ≤ 0)) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : ¬(n ≤ 0)) (hn : n ≤ 10000), Erdos261Prop n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : ¬(n ≤ 0)) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : ¬(n ≤ 0)) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : ¬(n ≤ 0)) (hn : n ≤ 10000), Erdos261Prop n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10000), Erdos261Prop n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10000), Erdos261Prop n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) ↔
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10000), Erdos261Prop n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n < 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n < 10000) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n < 10000))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n < 10000)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : n > 0) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 1 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : n ≤ 10000) :
    (0 < n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (n ≤ 10000) ∧ (¬((0 < n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 1 ≤ n) (hn : n ≤ 10001), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (n ≤ 10001) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (n ≤ 10001))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10002 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (n ≤ 10001)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn_pos : 0 < n), Erdos261Prop n) →
    (∀ {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000), Erdos261Prop n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) :
    (n ≤ 10000) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬((n ≤ 10000) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(10000 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(9999 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(10001 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((n ≤ 10000) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn_pos : 0 < n) (hn : n ≤ 10000) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
