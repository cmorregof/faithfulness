import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Curling Number Conjecture

*Reference:* [arxiv/0912.2382](https://arxiv.org/abs/0912.2382)
**The Curling Number Conjecture**
by *Benjamin Chaffin and N. J. A. Sloane*
-/

section

namespace Arxiv.«0912.2382»

/--
The curling number

Let $S$ be a finite nonempty sequence of integers. By grouping adjacent terms, it is always possible
to write it as $S = X Y Y . . . Y = X Y^k$, where $X$ and $Y$ are sequences of integers and $Y$ is nonempty
($X$ is allowed to be the empty sequence $∅$). There may be several ways to do this: choose the one
that maximizes the value of $k$: this $k$ is the curling number of $S$, denoted by $k S$.
-/
noncomputable def k (S : List ℤ) : ℕ :=
  sSup {k : ℕ | ∃ X Y : List ℤ, Y ≠ [] ∧ S = X ++ (List.replicate k Y).flatten}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r < L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≥ L.length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≥ r

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  omega

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (r ≤ L.length) ↔ (L.length ≥ r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≥ r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≥ r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≥ r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≥ r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : ¬(Y = [])) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  omega

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} :
    (Y ≠ []) ↔ (¬(Y = [])) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : ¬(Y = [])) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : ¬(Y = [])) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : ¬(Y = [])) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : ¬(Y = [])) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hL : L = X ++ (List.replicate r Y).flatten) (hY : Y ≠ []), r ≤ L.length

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hL : L = X ++ (List.replicate r Y).flatten) (hY : Y ≠ []), r ≤ L.length) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hL : L = X ++ (List.replicate r Y).flatten) (hY : Y ≠ []), r ≤ L.length) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hL : L = X ++ (List.replicate r Y).flatten) (hY : Y ≠ []), r ≤ L.length) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hL : L = X ++ (List.replicate r Y).flatten) (hY : Y ≠ []), r ≤ L.length) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY₀ : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY₀ : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY₀ : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY₀ : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) ↔
    (∀ {L X Y : List ℤ} {r : ℕ} (hY₀ : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length > r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), r ≤ L.length) →
    (∀ {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten), L.length ≤ r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {L X Y : List ℤ} {r : ℕ} (hY : Y ≠ []) (hL : L = X ++ (List.replicate r Y).flatten) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
