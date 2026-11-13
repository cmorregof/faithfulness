import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   notación `→g` (FCM.Combinatorics.Digraph.Tournament)
/-!
# Hedetniemi's conjecture (1966)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Hedetniemi%27s_conjecture)
* [He66] Hedetniemi, S. T. (1966). *Homomorphisms of graphs and automata.* Technical Report
  03105-44-T, University of Michigan.
* [ES85] El-Zahar, M. and Sauer, N. (1985). "The chromatic number of the product of two
  4-chromatic graphs is 4." *Combinatorica* 5, pp. 121--126.
* [Sh19] Shitov, Y. (2019). "Counterexamples to Hedetniemi's conjecture." *Ann. of Math.* 190,
  pp. 663--667. [arXiv:1905.02167](https://arxiv.org/abs/1905.02167)
* [Ta22] Tardif, C. (2022). "The chromatic number of the product of 14-chromatic graphs can
  be 13." *Combinatorica* 42, pp. 301--308.
* [Zh21] Zhu, X. (2021). "Relatively small counterexamples to Hedetniemi's conjecture."
  *J. Combin. Theory Ser. B* 146, pp. 141--150.
-/

section

open SimpleGraph

namespace HedetniemiConjecture

variable {α β : Type*}

/-- The **tensor (categorical) product** `G × H` of two simple graphs: `(a, b)` and `(c, d)` are
adjacent iff `a ~ c` in `G` and `b ~ d` in `H`. -/
def tensorProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

/-- The projection `G × H →g G` onto the first factor. -/
def tensorProd.fst (G : SimpleGraph α) (H : SimpleGraph β) : tensorProd G H →g G :=
  ⟨Prod.fst, fun h => h.1⟩

/-- The projection `G × H →g H` onto the second factor. -/
def tensorProd.snd (G : SimpleGraph α) (H : SimpleGraph β) : tensorProd G H →g H :=
  ⟨Prod.snd, fun h => h.2⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber < min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≥ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) :
    ((tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔ (min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≥ (tensorProd G H).chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H₀ : SimpleGraph β), (tensorProd G H₀).chromaticNumber ≤ min G.chromaticNumber H₀.chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H₀ : SimpleGraph β), (tensorProd G H₀).chromaticNumber ≤ min G.chromaticNumber H₀.chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H₀ : SimpleGraph β), (tensorProd G H₀).chromaticNumber ≤ min G.chromaticNumber H₀.chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H₀ : SimpleGraph β), (tensorProd G H₀).chromaticNumber ≤ min G.chromaticNumber H₀.chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) ↔
    (∀ (G : SimpleGraph α) (H₀ : SimpleGraph β), (tensorProd G H₀).chromaticNumber ≤ min G.chromaticNumber H₀.chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber > (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), (tensorProd G H).chromaticNumber ≤ min G.chromaticNumber H.chromaticNumber) →
    (∀ (G : SimpleGraph α) (H : SimpleGraph β), min G.chromaticNumber H.chromaticNumber ≤ (tensorProd G H).chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) (H : SimpleGraph β) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
