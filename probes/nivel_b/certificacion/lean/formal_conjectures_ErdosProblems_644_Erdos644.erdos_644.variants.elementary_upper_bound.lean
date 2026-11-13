import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Extremal
/-!
# Erdős Problem 644

*References:*
- [erdosproblems.com/644](https://www.erdosproblems.com/644)
- [EFKT92] Erdős, P. and Fon-Der-Flaass, D. and Kostochka, A. V. and Tuza, Zs., Small transversals in
  uniform hypergraphs. Siberian Adv. Math. (1992), 82-88.
-/

section

namespace Erdos644

open Filter Asymptotics

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (r ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr₀ : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr₀ : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr₀ : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr₀ : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr₀ : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : ¬(r < 3)), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (¬(r < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : ¬(r < 3)), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : ¬(r < 3)), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : ¬(r < 3)), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : ¬(r < 3)), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) :
    (3 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r > 3), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 4), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (r ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (r ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (r ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : r ≥ 3), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) > Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 < r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (3 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (3 < r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (3 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 4 ≤ r), ((2 * k : ℕ) : ℕ∞) ≥ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (4 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (4 ≤ r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (4 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), ((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (((2 * k : ℕ) : ℕ∞) ≤ Hypergraph.subfamilyTransversalBound k r 2)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 < ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ)  :
    (3 ≤ r) ↔ (2 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), (¬((3 ≤ r) ↔ (2 ≤ r))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((3 ≤ r) ↔ (2 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r : ℕ) (hr : 3 ≤ r), Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) →
    (∀ (k r : ℕ) (hr : 2 < r), Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(4 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), (3 ≤ r) ∧ (¬(Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ), ¬((Hypergraph.subfamilyTransversalBound k r 2 ≤ ((2 * k : ℕ) : ℕ∞)) ↔ (Hypergraph.subfamilyTransversalBound k r 2 ≥ ((2 * k : ℕ) : ℕ∞))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k r : ℕ) (hr : 3 ≤ r) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k r : ℕ) (hr : 3 ≤ r) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k r : ℕ) (hr : 3 ≤ r) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k r : ℕ) (hr : 3 ≤ r) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r : ℕ) (hr : 3 ≤ r) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
