import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Suffix-prefix avoidance bound

Let $A$ and $B$ be sets of words of length $n$ over an alphabet with $q$ letters. If no
(nonempty) suffix of any word in $A$ coincides with a prefix of any word in $B$, then
$$|A| \cdot |B| \leq \frac{q^{2n}}{en}.$$

*References:*
- [X post by Dmitry Rybin](https://x.com/DmitryRybin1/status/2027278135847428577)
- [Maximal sets of strings with no prefix-suffix overlap]
  (https://mathoverflow.net/questions/508648/maximal-sets-of-strings-with-no-prefix-suffix-overlap)
  by *Dmitry Rybin*, MathOverflow (2026)
- [An isoperimetric inequality for word overlap](https://arxiv.org/abs/2602.20143)
  by *Dmitrii Zakharov* (2026)
-/

section

open Finset Real

namespace SuffixPrefixAvoidance

variable {n q : ℕ}

/-- The suffix of a word `w : Fin n → Fin q` of length `k + 1` (the last `k + 1` characters). -/
def wordSuffix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨n - k - 1 + i, by omega⟩

/-- The prefix of a word `w : Fin n → Fin q` of length `k + 1` (the first `k + 1` characters). -/
def wordPrefix (w : Fin n → Fin q) (k : Fin n) : Fin (k + 1) → Fin q :=
  fun i => w ⟨i, by omega⟩

/-- Two sets of words $A, B$ over `Fin q` of length `n` are suffix-prefix avoiding if no
nonempty suffix of any word in $A$ equals any prefix of any word in $B$ of the same length. -/
def IsSuffixPrefixAvoiding (A B : Finset (Fin n → Fin q)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ k : Fin n, wordSuffix a k ≠ wordPrefix b k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    (0 < q) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((0 < q) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0 < q) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (q > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    ((A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔ ((q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hn : 0 < n) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq₀ : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq₀ : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq₀ : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq₀ : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq₀ : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : ¬(q ≤ 0)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) :
    (0 < q) ↔ (¬(q ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : ¬(q ≤ 0)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : ¬(q ≤ 0)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : ¬(q ≤ 0)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) ↔
    (∀ (A B : Finset (Fin n → Fin q)) (hq : ¬(q ≤ 0)) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card < (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (3 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : q > 0) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≥ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) > (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (3 * n) / (exp 1 * n) ≥ (A.card : ℝ) * B.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (q : ℝ) ^ (2 * n) / (exp 1 * n) ≤ (A.card : ℝ) * B.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) →
    (∀ (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B), (A.card : ℝ) * B.card ≤ (q : ℝ) ^ (2 * n) / (exp 1 * n)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (h : IsSuffixPrefixAvoiding A B) :
    (0 < n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ¬((0 < n) ↔ (True)) :=
  by norm_num

set_option maxHeartbeats 200000 in
example : ¬((0 < n) ↔ (True)) :=
  by decide

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (A B : Finset (Fin n → Fin q)) (hq : 0 < q) (hn : 0 < n) (h : IsSuffixPrefixAvoiding A B) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
