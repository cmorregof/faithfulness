import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1034

*References:*
- [erdosproblems.com/1034](https://www.erdosproblems.com/1034)
- [Er93] Erdős, Paul, *Some of my favorite solved and unsolved problems in graph theory*.
  Quaestiones Math. (1993), 333-350.
- [MaTa25] Ma, Jie and Tang, Quanyu, *On Erdős problem #1034*.
  [staff.ustc.edu.cn/~jiema/Erdos-1034.pdf](http://staff.ustc.edu.cn/~jiema/Erdos-1034.pdf)
-/

section

open Filter

namespace Erdos1034

/--
`JoinedToTwo G T Y` holds when every vertex of `Y` is joined to at least two (distinct)
vertices of `T`.
-/
def JoinedToTwo {V : Type*} (G : SimpleGraph V) (T Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ G.Adj y u ∧ G.Adj y v

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G₁ : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G₁.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G₁.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G₁ T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε₀ : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) →
    (∀ (ε : ℝ) (hε : ε > 0), ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)) ↔ (∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 5 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
