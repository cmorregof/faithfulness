import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 895

*References:*
- [erdosproblems.com/895](https://www.erdosproblems.com/895)
- [Er95d] Erdős, Paul, *On some problems in combinatorial set theory*. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61-65.
-/

section

open Filter

namespace Erdos895

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(18 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(17 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (18 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(18 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(17 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (18 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 19 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (19 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(18 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(17 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(20 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (19 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (n ≥ 18) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : n ≥ 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : n ≥ 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : n ≥ 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : n ≥ 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔ (∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a₁ b c : Set.Icc 1 n, a₁ ≠ b ∧ (a₁ : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a₁, b, c}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn₀ : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn₀ : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn₀ : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn₀ : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 18)) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (¬(n < 18)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : ¬(n < 18)) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : ¬(n < 18)) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : ¬(n < 18)) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : ¬(n < 18)) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 17 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) :
    (18 ≤ n) ↔ (17 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 17 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 17 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 17 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) ↔
    (∀ (n : ℕ) (hn : 17 < n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n > 18) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n > 18) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(18 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(17 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n > 18)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : n ≥ 19) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (n ≥ 19) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(18 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(17 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(20 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (n ≥ 19)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 17 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) →
    (∀ (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3), ∃ a b c : Set.Icc 1 n, a ≠ b ∧ (a : ℕ) + (b : ℕ) = c ∧ G.IsIndepSet {a, b, c}) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hG : G.CliqueFree 3) :
    (18 ≤ n) ↔ (17 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(18 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(17 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(19 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(16 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((18 ≤ n) ↔ (17 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hn : 18 ≤ n) (hG : G.CliqueFree 3) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hn : 18 ≤ n) (hG : G.CliqueFree 3) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hn : 18 ≤ n) (hG : G.CliqueFree 3) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hn : 18 ≤ n) (hG : G.CliqueFree 3) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (G : SimpleGraph (Set.Icc 1 n)) (hn : 18 ≤ n) (hG : G.CliqueFree 3) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
