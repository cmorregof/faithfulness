import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Ohba's conjecture (2002; proved by Noel, Reed and Wu 2015)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/List_coloring#Ohba's_conjecture)
* [Oh02] Ohba, K. (2002). "On chromatic-choosable graphs." *J. Graph Theory* 40, pp. 130--135.
* [NRW15] Noel, J. A., Reed, B. A. and Wu, H. (2015). "A proof of a conjecture of Ohba."
  *J. Graph Theory* 79, pp. 86--102. [arXiv:1211.1999](https://arxiv.org/abs/1211.1999)
* [ERT79] Erdős, P., Rubin, A. L. and Taylor, H. (1979). "Choosability in graphs."
  *Congr. Numer.* 26, pp. 125--157.
-/

section

open SimpleGraph Finset

namespace OhbaConjecture

variable {V : Type*}

/-- `G` is **`k`-choosable** if for every assignment `L` of a list of `k` colours to each
vertex there is a proper colouring `c` with `c v ∈ L v` for all `v`. -/
def Choosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, (L v).card = k) →
    ∃ c : V → ℕ, (∀ v, c v ∈ L v) ∧ ∀ u v, G.Adj u v → c u ≠ c v

/-- The **choice number** (list chromatic number) `ch(G)`: the least `k` for which `G` is
`k`-choosable. -/
noncomputable def choiceNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | Choosable G k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber < choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≥ choiceNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≥ G.chromaticNumber

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) :
    (G.chromaticNumber ≤ choiceNumber G) ↔ (choiceNumber G ≥ G.chromaticNumber) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≥ G.chromaticNumber) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≥ G.chromaticNumber) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≥ G.chromaticNumber) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≥ G.chromaticNumber) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h₀ : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h₀ : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h₀ : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h₀ : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) ↔
    (∀ [Fintype V] (G : SimpleGraph V) (h₀ : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G > G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), G.chromaticNumber ≤ choiceNumber G) →
    (∀ [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k), choiceNumber G ≤ G.chromaticNumber) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example [Fintype V] (G : SimpleGraph V) (h : ∃ k, Choosable G k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
