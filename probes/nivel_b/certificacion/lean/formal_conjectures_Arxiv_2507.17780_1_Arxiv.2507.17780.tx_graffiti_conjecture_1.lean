import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.AnnihilationNumber
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Residue
/-!
# TxGraffiti Conjecture 1: independence, annihilation, and residue

*Reference:* [arxiv/2507.17780](https://arxiv.org/abs/2507.17780)
**In Reverie Together: Ten Years of Mathematical Discovery with a Machine
Collaborator** by *Randy Davila, Boris Brimkov, Ryan Pepper*

Conjecture 1, the oldest of the four TxGraffiti conjectures in the cited
collection (open since 2016), asserts that every nontrivial connected graph $G$
with maximum degree $\Delta \ge 2$ satisfies
$$\alpha(G) \ge \frac{a(G) + R(G)}{\Delta(G)},$$
where $\alpha$ is the independence number, $a$ the annihilation number, $R$ the
Havel–Hakimi residue, and $\Delta$ the maximum degree.

This conjecture is **true**, proved in
[arXiv:2606.29553](https://arxiv.org/abs/2606.29553) (C. Gupta).
-/

section

open SimpleGraph

namespace Arxiv.«2507.17780»

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree < G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≥ G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree) :
    ((G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔ (G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) ↔
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≥ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum > (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), (G.annihilationNumber + residue G : ℝ) / G.maxDegree ≤ G.indepNum) →
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (_hConn : G.Connected) (_hDeg : 2 ≤ G.maxDegree), G.indepNum ≤ (G.annihilationNumber + residue G : ℝ) / G.maxDegree) := by
  intro h; intros; aesop

#eval "FIN_CERTIFICAR"
