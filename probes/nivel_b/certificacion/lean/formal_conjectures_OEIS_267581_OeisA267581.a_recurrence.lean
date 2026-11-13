import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Recurrence for Rule 167 cellular automaton sequence

Decimal representation of the middle column of the "Rule 167" elementary cellular automaton
starting with a single ON (black) cell.

*References:*
- [A267581](https://oeis.org/A267581)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA267581

open Nat Int

/-- The rule function for Rule 167. Inputs must be 0 or 1. -/
def caRule167 (c_L c_C c_R : ℕ) : ℕ :=
  let R : ℕ := 167
  let index : ℕ := 4 * c_L + 2 * c_C + c_R
  -- Rule 167 is determined by the index-th bit of R.
  (R / (2 ^ index)) % 2

/--
The state of the Rule 167 elementary cellular automaton at time $t$ and position $x$.
The initial condition is a single ON cell at $x=0$.
$C(t, x)$ is structurally recursive on $t$.
-/
def caState (t : ℕ) (x : ℤ) : ℕ :=
  match t with
  | 0 => if x = 0 then 1 else 0
  | t' + 1 =>
    let C_t' (y : ℤ) := caState t' y
    caRule167 (C_t' (x - 1)) (C_t' x) (C_t' (x + 1))

/-- The sequence of bits forming the middle column of the CA pattern, $C_{t, 0}$. -/
def middleColumnBit (t : ℕ) : ℕ := caState t 0

/--
Decimal representation of the middle column of the "Rule 167" elementary cellular automaton
starting with a single ON (black) cell.
The term $a(n)$ is the decimal value of the binary number $C_{0, 0} C_{1, 0} \dots C_{n, 0}$,
where $C_{i, 0}$ is the state of the center cell at time $i$.
$$a(n) = \sum_{k=0}^n C_{k, 0} \cdot 2^{n-k}$$
-/
def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k => (middleColumnBit k) * (2^ (n - k))

/-- The floor term in the conjectured recurrence relation for A267581.
This term, $\lfloor (1/2)^{(2^{n+1} \bmod n)} \rfloor$, simplifies to 1 if $(2^{n+1} \bmod n) = 0$
(i.e., $n \mid 2^{n+1}$), and 0 otherwise.
Since the recurrence is only stated for $n \ge 2$, the $n=0$ case is irrelevant
to the conjecture. -/
def oeisFloorTerm (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if (2 ^ (n + 1)) % n = 0 then 1 else 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : 1 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : 1 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : 1 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔
    (∀ (n : ℕ) (hn : 1 < n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n > 2), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : n ≥ 3), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) →
    (∀ (n : ℕ) (hn : 1 < n), a n = 3 * a (n - 1) + 1 - oeisFloorTerm n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = 2 * a (n - 1) + 1 - oeisFloorTerm n) ↔ (a n = 3 * a (n - 1) + 1 - oeisFloorTerm n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
