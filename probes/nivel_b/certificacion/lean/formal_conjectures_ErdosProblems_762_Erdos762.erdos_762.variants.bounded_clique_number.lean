import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.Vertex
/-!
# Erdős Problem 762

*References:*
- [erdosproblems.com/762](https://www.erdosproblems.com/762)
- [EGS90] Erdős, Paul and Gimbel, John and Straight, H. Joseph, *Chromatic number versus
  cochromatic number in graphs with bounded clique number*. European J. Combin. (1990), 235-240.
- [St24b] R. Steiner, *On the difference between the chromatic and cochromatic number*.
  arXiv:2408.02400 (2024).
-/

section

namespace Erdos762

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (2 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (2 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (2 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (2 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (2 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (2 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (2 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (2 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (2 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (2 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (2 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (2 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (2 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c3) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 3 < n), ∃ f : ℕ, ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), ∃ f : ℕ, ∀ (V : Type u_c6) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (n > 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : n > 2), ∃ f : ℕ, ∀ (V : Type u_c6) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : n > 2), ∃ f : ℕ, ∀ (V : Type u_c6) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : n > 2), ∃ f : ℕ, ∀ (V : Type u_c6) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : n > 2), ∃ f : ℕ, ∀ (V : Type u_c6) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f₁ : ℕ, ∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (∃ f : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔ (∃ f₁ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 2 < n), ∃ f₁ : ℕ, ∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 2 < n), ∃ f₁ : ℕ, ∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 2 < n), ∃ f₁ : ℕ, ∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 2 < n), ∃ f₁ : ℕ, ∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f₁) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c9) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c9) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn₀ : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c9) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn₀ : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c9) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn₀ : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c9) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn₀ : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n ≤ 2)), ∃ f : ℕ, ∀ (V : Type u_c12) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (¬(n ≤ 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), ∃ f : ℕ, ∀ (V : Type u_c12) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), ∃ f : ℕ, ∀ (V : Type u_c12) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), ∃ f : ℕ, ∀ (V : Type u_c12) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : ¬(n ≤ 2)), ∃ f : ℕ, ∀ (V : Type u_c12) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 < n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ f : ℕ, ∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ f : ℕ, ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c15) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n ≥ 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n ≥ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n ≥ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n ≥ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n ≥ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n ≥ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n ≥ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n ≥ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n ≥ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n ≥ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n ≥ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n ≥ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n ≥ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), ∃ f : ℕ, ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) →
    (∀ (n : ℕ) (hn : n > 3), ∃ f : ℕ, ∀ (V : Type u_c18) [Fintype V] (G : SimpleGraph V),
      G.CliqueFree n → G.chromaticNumber ≤ G.cochromaticNumber + f) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 < n) ↔ (n > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 < n) ↔ (n > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 < n) ↔ (n > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 < n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 < n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 < n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 < n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 < n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
