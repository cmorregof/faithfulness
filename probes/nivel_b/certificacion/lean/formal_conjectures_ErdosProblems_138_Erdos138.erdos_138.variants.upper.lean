import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.AP.Basic
/-!
# Erdős Problem 138

*References:*
- [erdosproblems.com/138](https://www.erdosproblems.com/138)
- [Be68] Berlekamp, E. R., A construction for partitions which avoid long arithmetic progressions. Canad. Math. Bull. (1968), 409-414.
- [Er80] Erdős, Paul, A survey of problems in combinatorial number theory. Ann. Discrete Math. (1980), 89-115.
- [Er81] Erdős, P., On the combinatorial problems which I would most like to see solved. Combinatorica (1981), 25-42.
- [Go01] Gowers, W. T., A new proof of Szemerédi's theorem. Geom. Funct. Anal. (2001), 465-588.
- [arxiv/2605.22763](https://arxiv.org/abs/2605.22763) *Advancing Mathematics Research with AI-Driven
  Formal Proof Search* by George Tsoukalas et al.
- [CFS26] Campos, M., Fox, J. and Schildkraut, C., A new lower bound for two-color van der Waerden
  numbers. [arXiv:2608.20824](https://arxiv.org/abs/2608.20824) (2026).
- [OAI26] OpenAI, *Quantitative Superexponential Bounds for van der Waerden Numbers*. OpenAI Math
  Release preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quantitative-Superexponential-Bounds-for-van-der-Waerden-Numbers-September-23-2026/paper.pdf
-/

section

open Nat Filter

namespace Erdos138

/--
The set of natural numbers that guarantee a monochromatic arithmetic progression.

A number `N` belongs to this set if, for a given number of colors `r` and an arithmetic
progression length `k`, any `r`-coloring of the integers `{1, ..., N}` must contain a
monochromatic arithmetic progression of length `k`.
-/
def monoAP_guarantee_set (r k : ℕ) : Set ℕ :=
  { N | ∀ coloring : Finset.Icc 1 N → Fin r, ContainsMonoAPofLength coloring k}

/--
The **van der Waerden number**, is the smallest integer `N` such that any `r`-coloring of
`{1, ..., N}` is guaranteed to contain a monochromatic arithmetic progression of
length `k`. It is defined as the infimum of the (non-empty) set of all such numbers `N`.
-/
noncomputable def monoAPNumber (r k : ℕ) : ℕ := sInf (monoAP_guarantee_set r k)

/--
An abbreviation for the van der Waerden number for 2 colors, commonly written as `W(k)`.
This represents the smallest integer `N` such that any 2-coloring of `{1, ..., N}`
must contain a monochromatic arithmetic progression of length `k`.
-/
noncomputable abbrev W : ℕ → ℕ := monoAPNumber 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k < 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≤ 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (W k ≥ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), ¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), ¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), ¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), ¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔
    (∀ (k : ℕ), ¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) < W k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) > W k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (3 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≥ W k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) →
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ), W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) →
    (∀ (k : ℕ), 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬(2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(9 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((W k ≤ 2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9)))) ↔ (2 ^ (2 ^ (2 ^ 2 ^ 2 ^ (k + 9))) ≤ W k)) :=
  ⟨(5 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
