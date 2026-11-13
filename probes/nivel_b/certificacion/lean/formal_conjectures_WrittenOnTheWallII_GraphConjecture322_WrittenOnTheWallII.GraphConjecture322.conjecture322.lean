import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.WellTotallyDominated
/-!
# Written on the Wall II - Conjecture 322

*Reference:*
[E. DeLaViña, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.uhd.edu/faculty/delavinae/research/wowII/)

The source applies the local-independence hypothesis to the complement graph. Its conclusion
also follows from the characterization of minimal total dominating sets of complete multipartite
graphs in [M. Subramanian and A. Selvakumar, *Total Domination and Minimal Total Domination
Polynomial of H-Join Graphs*](https://doi.org/10.2298/FIL2501267S).
-/

section

namespace WrittenOnTheWallII.GraphConjecture322

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (True))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (True))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 < Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (5 < Fintype.card α) := by
  plausible

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (5 < Fintype.card α))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (5 < Fintype.card α))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (5 < Fintype.card α)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (5 < Fintype.card α)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 6 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α) := by
  plausible

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (6 ≤ Fintype.card α)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) (hn : 5 ≤ Fintype.card α), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) (hn : 5 ≤ Fintype.card α), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) (hn : 5 ≤ Fintype.card α), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) (hn : 5 ≤ Fintype.card α), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) (hn : 5 ≤ Fintype.card α), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn₀ : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn₀ : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn₀ : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn₀ : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn₀ : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : ¬(Fintype.card α < 5)) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) :
    (5 ≤ Fintype.card α) ↔ (¬(Fintype.card α < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : ¬(Fintype.card α < 5)) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : ¬(Fintype.card α < 5)) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : ¬(Fintype.card α < 5)) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : ¬(Fintype.card α < 5)) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α > 5) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (Fintype.card α > 5))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (Fintype.card α > 5))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (Fintype.card α > 5)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (Fintype.card α > 5)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : Fintype.card α ≥ 6) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1), IsWellTotallyDominated G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    (5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6))) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) ∧ (¬((5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6))) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((5 ≤ Fintype.card α) ↔ (Fintype.card α ≥ 6)) :=
  by decide

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (_hG : G.Connected) (hn : 5 ≤ Fintype.card α) (h : ∀ v : α, indepNeighborsCard Gᶜ v ≤ 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
