import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Ramsey
/-!
# Erdős Problem 557

*References:*
- [erdosproblems.com/557](https://www.erdosproblems.com/557)
- [ErGr75] Erdős, P. and Graham, R. L., *On partition theorems for finite graphs*. Infinite and
  finite sets (Colloq., Keszthely, 1973), Vol. I, Colloq. Math. Soc. János Bolyai 10 (1975),
  515-527.
- [ReSt26] Reed, Bruce and Stein, Maya, *The Erdős-Sós conjecture in dense graphs*.
  [arXiv:2609.05417](https://arxiv.org/abs/2609.05417) (2026).
-/

section

open SimpleGraph

namespace Erdos557

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (k > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔ (k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hke : Even k) (hk : 0 < k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hke : Even k) (hk : 0 < k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hke : Even k) (hk : 0 < k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hke : Even k) (hk : 0 < k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hke : Even k) (hk : 0 < k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk₀ : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk₀ : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk₀ : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk₀ : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk₀ : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : ¬(k ≤ 0)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (¬(k ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : ¬(k ≤ 0)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : ¬(k ≤ 0)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : ¬(k ≤ 0)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : ¬(k ≤ 0)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) :
    (0 < k) ↔ (1 ≤ k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) ↔
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : k > 0) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 > multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 < n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (2 < n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≥ multicolourGraphRamsey k T) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), k * (n - 2) + 1 ≤ multicolourGraphRamsey k T) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T < k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    (0 < k) ↔ (1 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((0 < k) ↔ (1 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 3 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hno : Odd n) (hT : T.IsTree) :
    (2 ≤ n) ↔ (3 ≤ n) := by
  plausible

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
  ∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k n : ℕ) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≤ k * (n - 2) + 1) →
    (∀ (k n : ℕ) (hk : 1 ≤ k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (T : SimpleGraph (Fin n)) (hT : T.IsTree), multicolourGraphRamsey k T ≥ k * (n - 2) + 1) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k n : ℕ) (T : SimpleGraph (Fin n)) (hk : 0 < k) (hke : Even k) (hn : 2 ≤ n) (hno : Odd n) (hT : T.IsTree) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
