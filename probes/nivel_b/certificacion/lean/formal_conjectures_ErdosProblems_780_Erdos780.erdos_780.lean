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
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

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
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (1 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (1 < r))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

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
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : r ≥ 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (r ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : r ≥ 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : r ≥ 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : r ≥ 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : r ≥ 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔ (∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j₁, c (e j₁) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (ht : 1 ≤ t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr₀ : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr₀ : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr₀ : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr₀ : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr₀ : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : ¬(r < 1)) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (¬(r < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : ¬(r < 1)) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : ¬(r < 1)) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : ¬(r < 1)) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : ¬(r < 1)) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) :
    (1 ≤ r) ↔ (0 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) ↔
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : r > 1) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ r) ↔ (r > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ t) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ r) ↔ (r > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (r > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (r > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (r > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (r > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (r > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((1 ≤ r) ↔ (r > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 0 < r) (ht : 1 < t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (1 < t) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (1 < t))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (1 < t)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) →
    (∀ (n k r t : ℕ) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : {e : Finset (Fin n) // e.card = r} → Fin t), ∃ (i : Fin t) (e : Fin k → {e : Finset (Fin n) // e.card = r}),
      (∀ j, c (e j) = i) ∧ Pairwise fun a b ↦ Disjoint (e a).1 (e b).1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    (1 ≤ t) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ) (r : ℕ) (t : ℕ), (1 ≤ r) ∧ (k * r + (t - 1) * (k - 1) ≤ n) ∧ (¬((1 ≤ t) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (t : ℕ), ¬((1 ≤ t) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k r t : ℕ) (c : {e : Finset (Fin n) // e.card = r} → Fin t) (hr : 1 ≤ r) (ht : 1 ≤ t) (hn : k * r + (t - 1) * (k - 1) ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
