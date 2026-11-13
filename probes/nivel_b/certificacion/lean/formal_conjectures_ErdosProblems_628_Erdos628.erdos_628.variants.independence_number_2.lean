import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 628

*References:*
- [erdosproblems.com/628](https://www.erdosproblems.com/628)
- [BKPS09] Balogh, József and Kostochka, Alexandr V. and Prince, Noah and Stiebitz, Michael,
  *The Erdős-Lovász Tihany conjecture for quasi-line graphs*. Discrete Math. (2009), 3985-3991.
- [BrJu69] Brown, W. G. and Jung, H. A., *On odd circuits in chromatic graphs*. Acta Math. Acad.
  Sci. Hungar. (1969), 129-134.
- [Er68b] Erdős, P., *Problem 2*. Theory of Graphs (1968), 361.
- [So22] Song, Zi-Xia, *A survey on the Erdős-Lovász Tihany conjecture*. Adv. Math. (China)
  (2022), 259--274.
-/

section

namespace Erdos628

open SimpleGraph

/- ## Variants and partial results -/

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22 u_c23 u_c24 u_c25 u_c26 u_c27 u_c28 u_c29 u_c30 u_c31 u_c32 u_c33 u_c34
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c2) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c1) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c3) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c4) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c5) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c6) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (V : Type u_c9) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (2 ≤ a) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c7) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c8) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c10) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c11) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep₀ : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep₀ : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep₀ : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep₀ : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c13) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c14) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep₀ : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : ¬(a < 2)) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (V : Type u_c18) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (¬(a < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : ¬(a < 2)) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : ¬(a < 2)) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : ¬(a < 2)) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c16) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c17) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : ¬(a < 2)) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c19) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c20) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (V : Type u_c21) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) :
    (a ≥ 2) ↔ (a > 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c19) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c20) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c19) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c20) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c19) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c20) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c19) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) ↔
    (∀ (V : Type u_c20) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c22) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c23) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : 2 ≤ a) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c24) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c25) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c26) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 3) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c27) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (G.indepNum = 2) ↔ (G.indepNum = 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c29) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a > 1) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c28) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c30) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hab : a + b = k + 1) :
    (b ≥ 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 2) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 2) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 2) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 2) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 2) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (b : ℕ), ¬((b ≥ 2) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (V : Type u_c32) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_clique : G.CliqueFree k) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (a b : ℕ) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) →
    (∀ (V : Type u_c31) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hG_indep : G.indepNum = 2) (k : ℕ) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1), ∃ (s : Set V),
      (G.induce s).chromaticNumber ≥ (a : ℕ∞) ∧
      (G.induce sᶜ).chromaticNumber ≥ (b : ℕ∞)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c33) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (hb : b ≥ 2) (hab : a + b = k + 1) :
    (a ≥ 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (a : ℕ), ¬((a ≥ 2) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (V : Type u_c34) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (V : Type u_c34) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (V : Type u_c34) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (V : Type u_c34) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (V : Type u_c34) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (a b : ℕ) (hG_indep : G.indepNum = 2) (hG_chrom : G.chromaticNumber = (k : ℕ∞)) (hG_clique : G.CliqueFree k) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
