import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 981

*References:*
- [erdosproblems.com/981](https://www.erdosproblems.com/981)
- [El69] Elliott, P. D. T. A., *A conjecture of Erdős concerning character sums*.
  Indag. Math. 31 (1969), 164–171.
- [TaZh25] [arxiv/2512.24631](https://arxiv.org/abs/2512.24631)
  **Average first-passage times for character sums** by *Quanyu Tang and Hao Zhang*
-/

section

open Filter Real
open scoped Topology

namespace Erdos981

/--
Property of a natural $N$ to satisfy $\sum_{n\leq N} \left(\frac{n}{p}\right)<\epsilon N$,
where $\left(\frac{n}{p}\right)$ is the Jacobi symbol. The theorem statement mentions Legendre symbol,
however in formalization we use Jacobi symbol to avoid problem with passing the fact that $p$ is prime.
For prime $p$ `jacobiSym n p = legendreSym p n`.
-/
def Erdos981Property (ε : ℝ) (p : ℕ) (N : ℕ) : Prop :=
   (∑ n ≤ N, jacobiSym n p) < ε * N

/--
The smallest integer $m$ such that
$\sum_{n\leq N} \left(\frac{n}{p}\right)<\epsilon N$ for all $N\geq m$.
-/
noncomputable def f (ε : ℝ) (p : ℕ) : ℕ :=
  sInf { m | ∀ N ≥ m, Erdos981Property ε p N }

/--
The smallest integer $m$ such that $\sum_{n\leq m} \left(\frac{n}{p}\right)<\epsilon m$
-/
noncomputable def f' (ε : ℝ) (p : ℕ) : ℕ :=
  sInf { m | Erdos981Property ε p m }

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔ (∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c₁ > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c₁)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ c > (0 : ℝ), Tendsto (fun x ↦ (∑ p : Nat.primesBelow ⌈x⌉₊, f' ε p) * log x / x) atTop (𝓝 c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
