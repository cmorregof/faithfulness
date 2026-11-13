import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 820

*References:*
- [erdosproblems.com/820](https://www.erdosproblems.com/820)
- [Er74b] Erdős, P., *Remarks on some problems in number theory*. Math. Balkanica (1974),
  197-202.
- [OEIS A263647](https://oeis.org/A263647): the $n$ with $(2^n-1, 3^n-1) = 1$.
-/

section

open Filter

namespace Erdos820

/-- $H(n)$ is the smallest integer $l$ such that there is some $k < l$ with
$(k^n-1, l^n-1) = 1$.

We take $k$ and $l$ to be integers with $k \geq 2$, so that $k^n - 1 \geq 1$ for $n \geq 1$.
Smaller $k$ give degenerate values: over the integers $k = 0$ gives $(-1, l^n-1) = 1$, and $k = 1$
gives $(0, l^n-1) = l^n-1$, which is $1$ for $n = 1$, $l = 2$. Both would contradict the value
$H(1) = 3$ listed in the source.

For $n \geq 1$ the set is nonempty (see `Erdos820.H_spec`). For $n = 0$ it is empty, and
`H 0 = 0` by the `sInf ∅` convention; the only statement whose truth depends on `H 0` is
`Erdos820.H_eq_three_iff`, where both sides are false. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf {l : ℕ | ∃ k : ℕ, 2 ≤ k ∧ k < l ∧ Nat.Coprime (k ^ n - 1) (l ^ n - 1)}

/-- $K(n)$ is the smallest integer $k \geq 2$ such that $(k^n-1, 2^n-1) = 1$. As for
`Erdos820.H`, smaller $k$ are excluded because they give degenerate values.

For $n \geq 2$ the value $k = 2$ never works, and $k = 2^n - 1$ always works. For $n = 1$ we
get $K(1) = 2$, and for $n = 0$ the set is empty, so `K 0 = 0`. -/
noncomputable def K (n : ℕ) : ℕ :=
  sInf {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) (2 ^ n - 1)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (1 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k₁ : ℕ, 2 ≤ k₁ ∧ k₁ < H n ∧ Nat.Coprime (k₁ ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn₀ : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn₀ : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : ¬(n < 1)), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : ¬(n < 1)), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n > 1), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ}  :
    (1 ≤ n) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (n > 1)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : n ≥ 1), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} (hn : 1 ≤ n), ∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) →
    (∀ {n : ℕ} (hn : 0 < n), ∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (1 ≤ n) ∧ (¬(∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((∃ k : ℕ, 2 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1)) ↔ (∃ k : ℕ, 3 ≤ k ∧ k < H n ∧ Nat.Coprime (k ^ n - 1) (H n ^ n - 1))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} (hn : 1 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
