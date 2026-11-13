import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Fermat-Catalan conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Fermat-Catalan_conjecture)
-/

section

open scoped Function

namespace FermatCatalanConjecture

/--
The set of solutions to the Fermat-Catalan Conjecture, i.e. the
set of solutions $(a,b,c,m,n,k)$ to the equation $a^m + b^n = c^k$
where $\frac 1 m + \frac 1 n + \frac 1 k < 1$.
-/
def FermatCatalanSet' : Set (Fin 6 → ℕ) :=
    { f : Fin 6 → ℕ |
        (∀ i, 0 < f i) ∧
        (({0, 1, 2} : Set <| Fin 6).Pairwise (Nat.Coprime on f)) ∧
        (f 0) ^ (f 3) + (f 1) ^ (f 4) = (f 2) ^ (f 5) ∧
        ∑ i ∈ Finset.Icc 3 5, (1 / f i : ℝ) < 1 }
def FermatCatalanSet : Set (ℕ × ℕ × ℕ) :=
    (fun f => ((f 0) ^ (f 3), (f 1) ^ (f 4), (f 2) ^ (f 5))) '' FermatCatalanSet'

/-- The proposition that the Fermat-Catalan Conjecture is true. -/
def fermatCatalanConjecture : Prop :=
  FermatCatalanSet.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : m > 0) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (m > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : m > 0) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : m > 0) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : m > 0) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : m > 0) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hn : 0 < n) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm₀ : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm₀ : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm₀ : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm₀ : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm₀ : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : ¬(m ≤ 0)) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (¬(m ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : ¬(m ≤ 0)) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : ¬(m ≤ 0)) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : ¬(m ≤ 0)) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : ¬(m ≤ 0)) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 1 ≤ m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) :
    (0 < m) ↔ (1 ≤ m) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : 1 ≤ m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : 1 ≤ m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : 1 ≤ m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) ↔
    (∀ (m n k : ℕ) (hm : 1 ≤ m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 1 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < m) ↔ (1 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < n) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < m) ↔ (1 < m))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((0 < m) ↔ (1 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) →
    (∀ (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1), {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ a^m + b^n = c^k ∧
      ({a, b, c} : Set _).Pairwise Nat.Coprime}.Finite) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ) (n : ℕ) (k : ℕ), (0 < m) ∧ (0 < k) ∧ ((1 / m : ℝ) + 1 / n + 1 / k < 1) ∧ (¬((0 < n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((0 < n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (m n k : ℕ) (hm : 0 < m) (hn : 0 < n) (hk : 0 < k) (H : (1 / m : ℝ) + 1 / n + 1 / k < 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
