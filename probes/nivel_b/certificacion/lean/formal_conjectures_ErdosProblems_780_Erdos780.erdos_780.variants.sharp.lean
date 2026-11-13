import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 780

*References:*
- [erdosproblems.com/780](https://www.erdosproblems.com/780)
- [Er76] Erdős, Paul, _Problems and results in combinatorial analysis_. Colloquio Internazionale
  sulle Teorie Combinatorie (Roma, 1973), Tomo II (1976), 3-17.
- [Lo78] Lovász, L., _Kneser's conjecture, chromatic number, and homotopy_. J. Combin. Theory
  Ser. A (1978), 319-324.
- [AFL86] Alon, N. and Frankl, P. and Lovász, L., _The chromatic number of Kneser hypergraphs_.
  Trans. Amer. Math. Soc. (1986), 359-370.
-/

section

namespace Erdos780

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (1 < k))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : k ≥ 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (k ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : k ≥ 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : k ≥ 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : k ≥ 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : k ≥ 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c₁ : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c₁ (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk₀ : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk₀ : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk₀ : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk₀ : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk₀ : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : ¬(k < 1)) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (¬(k < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : ¬(k < 1)) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : ¬(k < 1)) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : ¬(k < 1)) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : ¬(k < 1)) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) :
    (1 ≤ k) ↔ (0 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : k > 1) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (1 ≤ k) ↔ (k > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (1 ≤ t) ∧ (¬((1 ≤ k) ↔ (k > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((1 ≤ k) ↔ (k > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 0 < k) (hr : 1 < r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (1 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (1 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (1 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (1 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (1 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (1 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (1 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t), ∃ c : {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) // e.card = r} → Fin t,
      ¬ ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin (k * r - 1 + (t - 1) * (k - 1))) //
          e.card = r}), (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) :
    (1 ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ k) ∧ (1 ≤ t) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k r t : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
