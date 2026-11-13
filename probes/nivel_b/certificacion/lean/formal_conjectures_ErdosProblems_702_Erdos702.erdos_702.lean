import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
/-!
# Erdős Problem 702

*References:*
- [erdosproblems.com/702](https://www.erdosproblems.com/702)
- [Er75f] Erdős, Paul, _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99-108.
- [Er76b] Erdős, P., _Problems and results in graph theory and combinatorial analysis_.
  Proceedings of the Fifth British Combinatorial Conference (Univ. Aberdeen, Aberdeen, 1975)
  (1976), 169-192.
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25-42.
- [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_. (1982),
  59--79.
- [Fr77] Frankl, Péter, _On families of finite sets no two of which intersect in a singleton_.
  Bull. Austral. Math. Soc. (1977), 125-134.
-/

section

open Filter Finset

namespace Erdos702

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A₁ ∈ 𝓕, ∃ B ∈ 𝓕, (A₁ ∩ B).card = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 4)), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k > 4), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) →
    (∀ (k : ℕ) (hk : 3 < k), ∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (4 ≤ k) ∧ (¬(∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 2).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1) ↔ (∀ᶠ n in atTop, ∀ 𝓕 : Finset (Finset (Fin n)), 𝓕.IsUniform k →
      (n - 3).choose (k - 2) < 𝓕.card → ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
