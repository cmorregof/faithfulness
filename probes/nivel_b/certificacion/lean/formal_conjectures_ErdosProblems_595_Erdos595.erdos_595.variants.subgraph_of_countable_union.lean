import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 595

*References:*
- [erdosproblems.com/595](https://www.erdosproblems.com/595)
- [Er87] Erdős, Paul, Problems and results on set systems and hypergraphs. Extremal problems
  for finite sets (Visegrád, 1991), Bolyai Soc. Math. Stud. (1994), 217-227.
- [Fo70] Folkman, Jon, Graphs with monochromatic complete subgraphs in every edge coloring.
  SIAM J. Appl. Math. (1970), 19:340-345.
- [NeRo75] Nešetřil, Jaroslav and Rödl, Vojtěch, Type theory of partition problems of graphs.
  Recent advances in graph theory (Proc. Second Czechoslovak Sympos., Prague, 1974),
  Academia, Prague (1975), 405-412.
-/

section

open SimpleGraph Set

namespace Erdos595
def IsCountableUnionOfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : ℕ → SimpleGraph V, (∀ i, (H i).CliqueFree 3) ∧ G = ⨆ i, H i

/-
## Main open problem
-/

/-
## Variants and partial results
-/

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c2} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c1} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c3} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c4} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c5} {G H : SimpleGraph V} (hH : H < G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c6} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (H < G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c7} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c8} {G H : SimpleGraph V} (hH : G ≥ H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type u_c9} {G H : SimpleGraph V} :
    (H ≤ G) ↔ (G ≥ H) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c8} {G H : SimpleGraph V} (hH : G ≥ H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c8} {G H : SimpleGraph V} (hH : G ≥ H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c8} {G H : SimpleGraph V} (hH : G ≥ H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c7} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c8} {G H : SimpleGraph V} (hH : G ≥ H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c10} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c11} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) (hH : H ≤ G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c11} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) (hH : H ≤ G), IsCountableUnionOfTriangleFree H) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c11} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) (hH : H ≤ G), IsCountableUnionOfTriangleFree H) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c11} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) (hH : H ≤ G), IsCountableUnionOfTriangleFree H) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c10} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c11} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) (hH : H ≤ G), IsCountableUnionOfTriangleFree H) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c13} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c14} {G H : SimpleGraph V} (hH₀ : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c14} {G H : SimpleGraph V} (hH₀ : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c14} {G H : SimpleGraph V} (hH₀ : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c14} {G H : SimpleGraph V} (hH₀ : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c13} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) ↔
    (∀ {V : Type u_c14} {G H : SimpleGraph V} (hH₀ : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c16} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c17} {G H : SimpleGraph V} (hH : G > H) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c18} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (G > H) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type u_c20} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) →
    (∀ {V : Type u_c19} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G), IsCountableUnionOfTriangleFree H) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c21} {G H : SimpleGraph V} (hG : IsCountableUnionOfTriangleFree G) :
    (H ≤ G) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type u_c22} {G H : SimpleGraph V} (hH : H ≤ G) (hG : IsCountableUnionOfTriangleFree G) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
