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
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 5)), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k > 5), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ (V : Type u) (G : SimpleGraph V), G.IsErdos944 k 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
