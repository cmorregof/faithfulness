import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.NumberTheory.AdditivelyComplete
/-!
# Erdős Problem 246

*References:*
- [erdosproblems.com/246](https://www.erdosproblems.com/246)
- [Bi59] Birch, B. J., *Note on a problem of Erd\H{o}s*. Proc. Cambridge
  Philos. Soc. (1959), 370-373.
- [Ca60] Cassels, J. W. S., *On the representation of integers as the sums of
  distinct summands taken from a fixed set*. Acta Sci. Math. (Szeged) (1960),
  111-124.
- [FaCh17] Fang, Jin-Hui and Chen, Yong-Gao, *A quantitative form of the
  {E}rd\H{o}s-{B}irch theorem*. Acta Arith. (2017), 301--311.
- [He00b] Hegyv\'{a}ri, N., *On the completeness of an exponential type
  sequence*. Acta Math. Hungar. (2000), 127--135.
- [Yu24] Yu, Wang-Xing, *On the representation of an exponential type sequence*.
  Publ. Math. Debrecen (2024), 253--261.
-/

section

namespace Erdos246

/-- The set $\{a^k b^l : k,l \geq 0\}$. -/
def Gamma (a b : ℕ) : Set ℕ :=
  {x | ∃ k l : ℕ, x = a ^ k * b ^ l}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (2 < a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (2 < a))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (2 < a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 3 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (3 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (3 ≤ a))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (3 ≤ a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : a ≥ 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (a ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : a ≥ 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : a ≥ 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : a ≥ 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : a ≥ 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (hb : 2 ≤ b) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha₀ : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha₀ : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha₀ : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha₀ : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha₀ : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : ¬(a < 2)) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (¬(a < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : ¬(a < 2)) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : ¬(a < 2)) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : ¬(a < 2)) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : ¬(a < 2)) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 1 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) :
    (2 ≤ a) ↔ (1 < a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) ↔
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a > 2) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a > 2))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : a ≥ 3) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (a ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (a ≥ 3))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (a ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 1 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    (2 ≤ a) ↔ (1 ≤ a) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ b) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ a) ↔ (1 ≤ a))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((2 ≤ a) ↔ (1 ≤ a)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 2 < b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (2 < b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (2 < b))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (2 < b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 1 < a) (hb : 3 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (3 ≤ b) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(4 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(4 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(3 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(4 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(4 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(4 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (3 ≤ b))) :=
  ⟨(0 : ℕ), (4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (3 ≤ b)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) →
    (∀ (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b), IsAddComplete (Gamma a b)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hab : Nat.Coprime a b) :
    (2 ≤ b) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(10 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ) (b : ℕ), (2 ≤ a) ∧ (Nat.Coprime a b) ∧ (¬((2 ≤ b) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((2 ≤ b) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : Nat.Coprime a b) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
