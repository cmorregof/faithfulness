import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 434

*References:*
- [erdosproblems.com/434](https://www.erdosproblems.com/434)
- [Ki02] Kiss, G., On the extremal Frobenius problem in a new aspect. Ann. Univ. Sci.
  Budapest. Eötvös Sect. Math. (2002), 139–142.
-/

section

namespace Erdos434

open Erdos434 Finset

/--
A natural $n$ is representable as a set $A$ if it can be
written as the sum of finitely many elements of $A$
(with repetition allowed).
-/
abbrev Nat.IsRepresentableAs (n : ℕ) (A : Set ℕ) :=
    ∃ (S : Multiset ℕ), (∀ a ∈ S, a ∈ A) ∧ S.sum = n

/--
The number of naturals that cannot be written as the sum of
finitely many elements of the set $A$, with repetition allowed.
-/
noncomputable abbrev Nat.NcardUnrepresentable (A : Set ℕ) :=
    { n : ℕ | ¬n.IsRepresentableAs A }.ncard
def erdos_434.parts.i.answer (n : ℕ) (k : ℕ) : Set ℕ := Set.Icc (n - k + 1 : ℕ) n

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (1 < n))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

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
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : n ≥ 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn₀ : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn₀ : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn₀ : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn₀ : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn₀ : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : ¬(n < 1)) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : ¬(n < 1)) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : ¬(n < 1)) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : ¬(n < 1)) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : ¬(n < 1)) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) ↔
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n > 1) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hk : 2 ≤ k) (h : k ≤ n) :
    (1 ≤ n) ↔ (n > 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (2 ≤ k) ∧ (k ≤ n) ∧ (¬((1 ≤ n) ↔ (n > 1))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

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
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : n ≥ 1) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 2 < k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (2 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (2 < k))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (2 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 0 < n) (hk : 3 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) →
    (∀ (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n), IsGreatest
      { Nat.NcardUnrepresentable S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 n)
        (_ : #S = k) (_ : S.gcd id = 1) }
      (Nat.NcardUnrepresentable <| erdos_434.parts.i.answer n k)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (h : k ≤ n) :
    (2 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (k ≤ n) ∧ (¬((2 ≤ k) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((2 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (hn : 1 ≤ n) (hk : 2 ≤ k) (h : k ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
