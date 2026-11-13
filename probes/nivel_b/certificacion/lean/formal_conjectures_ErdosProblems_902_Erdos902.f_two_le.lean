import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Digraph.Tournament
/-!
# Erdős Problem 902

*References:*
- [erdosproblems.com/902](https://www.erdosproblems.com/902)
- [Er63c] Erdős, P., *On a problem in graph theory*. Math. Gaz. 47 (1963), 220-223.
  [PDF](https://www.renyi.hu/~p_erdos/1963-08.pdf)
- [Er82e] Erdős, Paul, *Some of my favourite problems which recently have been solved*.
  (1982), 59-79.
- [SzSz65] Szekeres, E. and Szekeres, G., *On a problem of Schütte and Erdős*. Math. Gaz. 49
  (1965), 290-293.
-/

section

open Filter Asymptotics

namespace Erdos902

/-- `HasPropertyS G n` is Schütte's property $S_n$ [Er63c]: every set `E` of `n` vertices is
dominated by a vertex outside it, that is, some vertex `x ∉ E` has an edge to every vertex of
`E`. -/
def HasPropertyS {V : Type*} (G : Digraph V) (n : ℕ) : Prop :=
  ∀ E : Finset V, E.card = n → ∃ x ∉ E, ∀ e ∈ E, G.Adj x e

/-- $f(n)$: the least number of vertices of a tournament with property $S_n$.

A tournament with fewer than $n$ vertices has no set of $n$ vertices, so it has property $S_n$
vacuously; the condition `n ≤ m` excludes this case. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ ∃ G : Digraph (Fin m), G.IsTournament ∧ HasPropertyS G n}

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 < 7

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 < 7) →
    (f 2 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(f 2 < 7)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(f 2 < 7)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (f 2 < 7)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (f 2 < 7)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  f 3 ≤ 7

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 3 ≤ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 3 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(f 3 ≤ 7)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(f 3 ≤ 7)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (f 3 ≤ 7)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (f 3 ≤ 7)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≥ 7

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≥ 7) →
    (f 2 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (f 2 ≥ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(f 2 ≥ 7)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(f 2 ≥ 7)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (f 2 ≥ 7)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (f 2 ≥ 7)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  7 ≥ f 2

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (7 ≥ f 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (7 ≥ f 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (7 ≥ f 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (7 ≥ f 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (7 ≥ f 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  ¬(7 < f 2)

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  omega

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example  :
    (f 2 ≤ 7) ↔ (¬(7 < f 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (¬(7 < f 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (¬(7 < f 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (¬(7 < f 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) ↔
    (¬(7 < f 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  7 > f 2

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (7 > f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(7 > f 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(7 > f 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (7 > f 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (7 > f 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  8 ≥ f 2

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (8 ≥ f 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(8 ≥ f 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(8 ≥ f 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (8 ≥ f 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (8 ≥ f 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  f 2 ≤ 7

set_option maxHeartbeats 200000 in
example : Prop :=
  7 ≤ f 2

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (7 ≤ f 2) →
    (f 2 ≤ 7) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (f 2 ≤ 7) →
    (7 ≤ f 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : (¬(7 ≤ f 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : (¬(7 ≤ f 2)) :=
  by decide

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (7 ≤ f 2)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((f 2 ≤ 7) ↔ (7 ≤ f 2)) :=
  by decide

#eval "FIN_CERTIFICAR"
