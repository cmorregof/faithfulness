import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Representation of sequence terms by harmonic numbers $\lfloor \frac{1}{2H(n) - H(n^2+n-1) - \gamma} \rfloor$

A227582: Expansion of $(2+3x+2x^2+2x^3+3x^4+x^5-x^6)/(1-2x+x^2-x^5+2x^6-x^7)$.

The sequence satisfies the linear recurrence:
$$a(n) = 2 a(n-1) - a(n-2) + a(n-5) - 2 a(n-6) + a(n-7)$$
with initial values $a(1) = 2, a(2) = 7, a(3) = 14, a(4) = 23, a(5) = 35, a(6) = 50, a(7) = 67$.

The sequence is 1-indexed in OEIS, so $a(n)$ is the $(n-1)$-th term of the 0-indexed solution.

*References:*
- [A227582](https://oeis.org/A227582)
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven Formal Proof Search* by George Tsoukalas et al.
-/

section

namespace OeisA227582

open BigOperators LinearRecurrence

/--
The sequence $b_n$ such that $A227582(n) = b_{n-1}$ for $n \ge 1$.
This is the 0-indexed solution to the linear recurrence in $\mathbb{Z}$.
-/
def baseSeq (n : ℕ) : ℤ :=
  let order := 7
  -- Coefficients $c_i$ for the recurrence $u_{n+7} = \sum_{i=0}^6 c_i u_{n+i}$.
  -- This corresponds to the OEIS signature $(2, -1, 0, 0, 1, -2, 1)$ which means $c_i = s_{7-i}$.
  let coeffs : Fin order → ℤ := ![1, -2, 1, 0, 0, -1, 2]
  -- Initial values $a_zero$ through $a_6$. These are {2, 7, 14, 23, 35, 50, 67}.
  let init : Fin order → ℤ := ![2, 7, 14, 23, 35, 50, 67]
  let E : LinearRecurrence ℤ := { order := order, coeffs := coeffs }
  E.mkSol init n

/--
Expansion of $(2+3x+2x^2+2x^3+3x^4+x^5-x^6)/(1-2x+x^2-x^5+2x^6-x^7)$, 1-indexed.
-/
def a (n : ℕ) : ℕ :=
  if 0 < n then
    (baseSeq (n - 1)).toNat
  else
    0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (n > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn₀ : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (¬(n ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 0)), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (0 < n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : n > 0), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 0 < n), a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) →
    (∀ (n : ℕ) (hn : 1 ≤ n), a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (0 < n) ∧ (¬(a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((a n = (Int.floor (1 / (2 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat) ↔ (a n = (Int.floor (1 / (3 * (↑(harmonic n) : ℝ) -
    (↑(harmonic (n * n + n - 1)) : ℝ) - Real.eulerMascheroniConstant))).toNat)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 0 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
