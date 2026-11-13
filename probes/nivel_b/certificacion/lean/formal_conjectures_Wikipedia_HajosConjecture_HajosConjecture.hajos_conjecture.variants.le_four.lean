import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Hajós' conjecture (1961) — disproved

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Hadwiger_conjecture_(graph_theory)#Generalizations)
* [Ha61] Hajós, G. (1961). "Über eine Konstruktion nicht n-färbbarer Graphen."
  *Wiss. Z. Martin-Luther-Univ. Halle-Wittenberg Math.-Natur. Reihe* 10, pp. 116--117.
* [Di52] Dirac, G. A. (1952). "A property of 4-chromatic graphs and some remarks on critical
  graphs." *J. London Math. Soc.* 27, pp. 85--92.
* [Ca79] Catlin, P. A. (1979). "Hajós' graph-coloring conjecture: variations and
  counterexamples." *J. Combin. Theory Ser. B* 26, pp. 268--274.
* [EF81] Erdős, P. and Fajtlowicz, S. (1981). "On the conjecture of Hajós." *Combinatorica* 1,
  pp. 141--143.
* [Th05] Thomassen, C. (2005). "Some remarks on Hajós' conjecture." *J. Combin. Theory Ser. B*
  93, pp. 95--105.
-/

section

open SimpleGraph

namespace HajosConjecture

variable {V W : Type*}

/-- A **subdivision model** of `H` in `G`: an injective map `f` of the vertices of `H` to
*branch vertices* of `G`, together with, for each edge `w w'` of `H`, a path in `G` from
`f w` to `f w'` whose internal vertices avoid all branch vertices and are disjoint from the
internal vertices of the paths of all other edges. -/
structure IsSubdivisionModel (H : SimpleGraph W) (G : SimpleGraph V) (f : W → V)
    (P : ∀ w w', H.Adj w w' → G.Walk (f w) (f w')) : Prop where
  injective : Function.Injective f
  isPath : ∀ w w' h, (P w w' h).IsPath
  internal_avoid : ∀ w w' h x, x ∈ (P w w' h).support.tail.dropLast → x ∉ Set.range f
  internal_disjoint : ∀ w₁ w₁' h₁ w₂ w₂' h₂, s(w₁, w₁') ≠ s(w₂, w₂') →
    ∀ x, x ∈ (P w₁ w₁' h₁).support.tail.dropLast → x ∉ (P w₂ w₂' h₂).support.tail.dropLast

/-- `G` contains a **subdivision** of `H` (i.e. `H` is a topological minor of `G`). -/
def ContainsSubdivision (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ (f : W → V) (P : ∀ w w', H.Adj w w' → G.Walk (f w) (f w')), IsSubdivisionModel H G f P

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k < 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k < 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (k ≤ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (k ≤ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (4 ≥ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk₀ : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk₀ : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk₀ : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk₀ : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk₀ : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : ¬(4 < k)) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (¬(4 < k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : ¬(4 < k)) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : ¬(4 < k)) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : ¬(4 < k)) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : ¬(4 < k)) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (k ≤ 4) ↔ (k < 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) ↔
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 4 > k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (4 > k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (4 > k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 5 ≥ k) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    (k ≤ 4) ↔ (5 ≥ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((k ≤ 4) ↔ (5 ≥ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k < 5) (h : (k : ℕ∞) < G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ ((k : ℕ∞) < G.chromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4), ContainsSubdivision (completeGraph (Fin k)) G) →
    (∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber), ContainsSubdivision (completeGraph (Fin k)) G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) :
    ((k : ℕ∞) ≤ G.chromaticNumber) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : k ≤ 4) (h : (k : ℕ∞) ≤ G.chromaticNumber) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
