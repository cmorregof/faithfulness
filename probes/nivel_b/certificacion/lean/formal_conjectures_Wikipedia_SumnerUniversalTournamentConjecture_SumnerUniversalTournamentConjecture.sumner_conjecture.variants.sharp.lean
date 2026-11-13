import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Digraph.Tournament
--   notación `→g` (FCM.Combinatorics.Digraph.Tournament)
/-!
# Sumner's universal tournament conjecture (1971)

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Sumner%27s_conjecture)
* [HT91] Häggkvist, R. and Thomason, A. (1991). "Trees in tournaments." *Combinatorica* 11,
  pp. 123--130.
* [ES04] El Sahili, A. (2004). "Trees in tournaments." *J. Combin. Theory Ser. B* 92,
  pp. 183--187.
* [KMO11] Kühn, D., Mycroft, R. and Osthus, D. (2011). "A proof of Sumner's universal
  tournament conjecture for large tournaments." *Proc. London Math. Soc.* 102, pp. 731--766.
  [arXiv:1010.4430](https://arxiv.org/abs/1010.4430)
-/

section

open SimpleGraph Digraph

namespace SumnerUniversalTournamentConjecture

/-- An **oriented tree**: a digraph that is an orientation of a tree. -/
def IsOrientedTree {W : Type*} (D : Digraph W) : Prop :=
  ∃ T : SimpleGraph W, T.IsTree ∧ D.IsOrientation T

/-- The digraph `D` **embeds** in `D'`: there is an injective digraph homomorphism `D →g D'`. -/
def Embeds {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (D : Digraph W) (D' : Digraph V) : Prop :=
  ∃ f : D →g D', Function.Injective f

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (2 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (2 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 3 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (3 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (3 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (n ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : n ≥ 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn₀ : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 2)), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (¬(n < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : ¬(n < 2)), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (2 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n > 2), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : n ≥ 3), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (n ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (n ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (n ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (2 ≤ n) ↔ (1 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((2 ≤ n) ↔ (1 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((2 ≤ n) ↔ (1 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) →
    (∀ (n : ℕ) (hn : 1 < n), ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (2 ≤ n) ∧ (¬(∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 2 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G) ↔ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (D : Digraph W) (_ : DecidableRel D.Adj),
      Fintype.card W = n ∧ IsOrientedTree D ∧
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Digraph V) (_ : DecidableRel G.Adj),
        Fintype.card V = 3 * n - 3 ∧ G.IsTournament ∧ ¬ Embeds D G)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 2 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
