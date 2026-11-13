import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.AP.Basic
--   notación asintótica `≪` (FCM.Analysis.Asymptotics.Basic)
/-!
# Erdős Problem 3

*References:*
- [erdosproblems.com/3](https://www.erdosproblems.com/3)
- [BlSi20] Bloom, Thomas F. and Sisask, Olof, *Breaking the logarithmic barrier in Roth's theorem
  on arithmetic progressions*. arXiv:2007.03528 (2020).
- [Go01] Gowers, W. T., *A new proof of Szemerédi's theorem*. Geom. Funct. Anal. (2001), 465-588.
- [GrTa17] Green, Ben and Tao, Terence, *New bounds for Szemerédi's theorem, III: a
  polylogarithmic bound for $r_4(N)$*. Mathematika (2017).
- [KeMe23] Kelley, Zander and Meka, Raghu, *Strong bounds for 3-progressions*. 2023 IEEE 64th
  Annual Symposium on Foundations of Computer Science (FOCS) (2023).
- [LSS24] Leng, James, Sah, Ashwin and Sawhney, Mehtaab, *Improved bounds for Szemerédi's
  theorem*. arXiv:2402.17995 (2024).
- [OAI26] OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf
-/

section

open Asymptotics Filter

namespace Erdos3

/--
$r_k(N)$ is the largest size of a subset of $\{1, \dots, N\}$ that does not contain a non-trivial
$k$-term arithmetic progression.
-/
noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (5 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (5 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (5 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 6 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (6 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (6 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (6 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔ (∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c₁ > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c₁)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk₀ : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 5)), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (¬(k < 5)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : ¬(k < 5)), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (5 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) ↔
    (∀ (k : ℕ) (hk : 4 < k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k > 5), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k > 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k > 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k > 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : k ≥ 6), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (k ≥ 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (k ≥ 6))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (k ≥ 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c > (0 : ℝ),
    (fun N ↦ (r k N : ℝ)) ≪
      fun N : ℕ ↦ (N : ℝ) * Real.exp (-Real.log (Real.log N) ^ c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (5 ≤ k) ↔ (4 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((5 ≤ k) ↔ (4 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((5 ≤ k) ↔ (4 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 5 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
