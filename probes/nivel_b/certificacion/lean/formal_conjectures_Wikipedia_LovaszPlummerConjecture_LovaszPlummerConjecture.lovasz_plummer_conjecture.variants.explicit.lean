import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Cycle
/-!
# The Lovász–Plummer conjecture (proved 2011) and Sheehan's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [LP86] Lovász, L. and Plummer, M. D. (1986). *Matching Theory.* North-Holland.
* [EKKKN11] Esperet, L., Kardoš, F., King, A. D., Král', D. and Norine, S. (2011).
  "Exponentially many perfect matchings in cubic graphs." *Adv. Math.* 227, pp. 1646--1664.
  [arXiv:1012.2878](https://arxiv.org/abs/1012.2878)
* [Sh77] Sheehan, J. (1977). "The multiplicity of Hamiltonian circuits in a graph." In *Recent
  Advances in Graph Theory*, Academia, Prague, pp. 477--480.
* [Th98] Thomassen, C. (1998). "Independent dominating sets and a second Hamiltonian cycle in
  regular graphs." *J. Combin. Theory Ser. B* 72, pp. 104--109.
-/

section

open SimpleGraph

namespace LovaszPlummerConjecture

variable {V : Type*}

/-- The number of perfect matchings of `G`. -/
noncomputable def perfectMatchingCount (G : SimpleGraph V) : ℕ :=
  {M : G.Subgraph | M.IsPerfectMatching}.ncard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) < perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≥ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔ (perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hbridgeless : G.IsBridgeless) (hcubic : ∀ v, G.degree v = 3), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hbridgeless : G.IsBridgeless) (hcubic : ∀ v, G.degree v = 3), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hbridgeless : G.IsBridgeless) (hcubic : ∀ v, G.degree v = 3), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hbridgeless : G.IsBridgeless) (hcubic : ∀ v, G.degree v = 3), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hbridgeless : G.IsBridgeless) (hcubic : ∀ v, G.degree v = 3), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic₀ : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic₀ : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic₀ : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic₀ : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic₀ : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G > (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≥ (3 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656) ≤ perfectMatchingCount G) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless), perfectMatchingCount G ≤ (2 : ℝ) ^ ((Fintype.card V : ℝ) / 3656)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hcubic : ∀ v, G.degree v = 3) (hbridgeless : G.IsBridgeless) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
