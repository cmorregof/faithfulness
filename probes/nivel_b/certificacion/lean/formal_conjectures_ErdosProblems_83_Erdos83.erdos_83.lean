import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 83

*References:*
- [erdosproblems.com/83](https://www.erdosproblems.com/83)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [Er90] Erdős, Paul, *Some of my favourite unsolved problems*. A tribute to Paul Erdős (1990),
  467-478.
- [Er92e] Erdős, Pál, *Some Unsolved problems in Geometry, Number Theory and Combinatorics*.
  Eureka (1992), 44-48.
- [Er95] Erdős, Paul, *Some of my favourite problems in number theory, combinatorics, and
  geometry*. Resenhas (1995), 165-186.
- [ErKoRa61] Erdős, P. and Ko, Chao and Rado, R., *Intersection theorems for systems of finite
  sets*. Quart. J. Math. Oxford Ser. (2) (1961), 313-320.
- [AhKh97] Ahlswede, Rudolf and Khachatrian, Levon H., *The complete intersection theorem for
  systems of finite sets*. European J. Combin. (1997), 125-136.
-/

section

namespace Erdos83

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card < ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≥ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) :
    (F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔ (((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) (hF : ∀ A ∈ F, A.card = 2 * n), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) (hF : ∀ A ∈ F, A.card = 2 * n), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) (hF : ∀ A ∈ F, A.card = 2 * n), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) (hF : ∀ A ∈ F, A.card = 2 * n), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) (hF : ∀ A ∈ F, A.card = 2 * n), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF₀ : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF₀ : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF₀ : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF₀ : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) ↔
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF₀ : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 > F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) :
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) ↔ (∀ A ∈ F, ∀ B ∈ F, 2 < (A ∩ B).card) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 3 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≥ F.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    (∀ A ∈ F, A.card = 2 * n) ↔ (∀ A ∈ F, A.card = 3 * n) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), F.card ≤ ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2) →
    (∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card), ((4 * n).choose (2 * n) - (2 * n).choose n ^ 2) / 2 ≤ F.card) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (F : Finset (Finset (Fin (4 * n)))) (hF : ∀ A ∈ F, A.card = 2 * n) (hinter : ∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
