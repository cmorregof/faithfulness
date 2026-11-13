import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 416

*References:*
- [erdosproblems.com/416](https://www.erdosproblems.com/416)
- [OAI26a] OpenAI, *An asymptotic formula for the number of totients*. OpenAI Math Release
  preprint (2026).
  https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/An-asymptotic-formula-for-the-number-of-totients-September-25-2026.pdf
-/

section

open Filter
open scoped Topology Real

namespace Erdos416

/-- Let `V(x)` count the number of `n≤x` such that `ϕ(m)=n` is solvable. -/
noncomputable abbrev V (x : ℝ) : ℝ :=
  open scoped Classical in
  (Finset.Icc 1 ⌊x⌋₊ |>.filter (fun n => ∃ (m : ℕ), m.totient = n)).card

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 ≤ c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  simp_all

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (0 ≤ c) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (0 ≤ c))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (0 ≤ c))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (0 ≤ c))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (0 ≤ c))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (0 ≤ c))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (0 ≤ c))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (0 ≤ c)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (0 ≤ c)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (0 ≤ c)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (0 ≤ c)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (0 ≤ c)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (0 ≤ c)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : c > 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (c > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : c > 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : c > 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : c > 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : c > 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc₀ : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc₀ : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc₀ : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc₀ : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc₀ : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : ¬(c ≤ 0)), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (c : ℝ) :
    (0 < c) ↔ (¬(c ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : ¬(c ≤ 0)), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : ¬(c ≤ 0)), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : ¬(c ≤ 0)), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) ↔
    (∀ (c : ℝ) (hc : ¬(c ≤ 0)), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (c : ℝ) (hc : c ≥ 0), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) →
    (∀ (c : ℝ) (hc : 0 < c), Filter.Tendsto (fun x => V (c * x) / V x) Filter.atTop (𝓝 c)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (c : ℝ)  :
    (0 < c) ↔ (c ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (c ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (c ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (c ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (c ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (c ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), (¬((0 < c) ↔ (c ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (c ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (c ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (c ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (c ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (c ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (c : ℝ), ¬((0 < c) ↔ (c ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 < c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 < c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 < c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 < c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (c : ℝ) (hc : 0 < c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
