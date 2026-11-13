import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Meyniel's conjecture on the cop number

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Cop_number)
* [Fr87] Frankl, P. (1987). "Cops and robbers in graphs with large girth and Cayley graphs."
  *Discrete Appl. Math.* 17, pp. 301--305.
* [NW83] Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
  *Discrete Math.* 43, pp. 235--239.
* [SS11] Scott, A. and Sudakov, B. (2011). "A bound for the cops and robbers problem."
  *SIAM J. Discrete Math.* 25, pp. 1438--1442.
* [BB12] Baird, W. and Bonato, A. (2012). "Meyniel's conjecture on the cop number: a survey."
  *J. Comb.* 3, pp. 225--238.
-/

section

open Filter

namespace MeynielConjecture

variable {V : Type*}

/-- A **move** in the cops-and-robbers game: stay put, or slide along an edge. -/
def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

/-- `CopsCatchWithin G k m c r`: with `k` cops at positions `c`, the robber at `r`, and the cops
to move, the cops can guarantee to catch the robber within `m` further rounds. In each round
every cop moves (or stays), catching the robber if a cop reaches the robber's vertex, and then
the robber moves (or stays). -/
def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

/-- `k` cops have a winning strategy on `G`: they can choose starting positions such that,
wherever the robber starts, they catch the robber in finitely many rounds. -/
def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

/-- The **cop number** `c(G)`: the least number of cops that can guarantee to catch the
robber on `G`. -/
noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G < Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≥ Fintype.card V) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≥ copNumber G

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (copNumber G ≤ Fintype.card V) ↔ (Fintype.card V ≥ copNumber G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) ↔
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≥ copNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) ↔
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≥ copNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) ↔
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≥ copNumber G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) ↔
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≥ copNumber G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V > copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V), copNumber G ≤ Fintype.card V) →
    (∀ [Fintype V] (G : SimpleGraph V), Fintype.card V ≤ copNumber G) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
