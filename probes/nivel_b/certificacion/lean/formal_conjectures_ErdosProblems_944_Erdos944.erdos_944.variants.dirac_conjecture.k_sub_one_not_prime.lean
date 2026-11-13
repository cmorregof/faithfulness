import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
/-!
# Erdős Problem 944

*Reference:* [erdosproblems.com/944](https://www.erdosproblems.com/944)
-/

section

universe u
variable {V : Type u}

namespace Erdos944

open Erdos944

/--
The predicate that graph $G$ with chromatic number $k$ is such that every vertex is critical, yet
every critical set of edges has size $>r$
-/
def SimpleGraph.IsErdos944 (G : SimpleGraph V) (k r : ℕ) : Prop :=  G.IsCritical k ∧
    (∀ (edges : Set (Sym2 V)), G.IsCriticalEdges edges → r < edges.ncard)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 4) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (h : ¬ (k - 1).Prime) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 4)) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 3 < k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 3 < k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 3 < k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 3 < k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (h : ¬ (k - 1).Prime) :
    (4 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬ (k - 1).Prime) ∧ (¬((4 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) (h : ¬ (k - 1).Prime) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
