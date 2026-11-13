import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The burning number conjecture

*References:*
* [BJR16] Bonato, A., Janssen, J., and Roshanbin, E. (2016). "How to burn a graph."
  *Internet Math.* 12, pp. 85--100.
  [arXiv:1507.06524](https://arxiv.org/abs/1507.06524)
* [NT24] Norin, S. and Turcotte, J. (2024). "The burning number conjecture holds
  asymptotically." *J. Combin. Theory Ser. B* 168, pp. 208--235.
  [arXiv:2207.04035](https://arxiv.org/abs/2207.04035)
-/

section

namespace BurningNumberConjecture

variable {V : Type*}

/-- The ball-cover condition for burning a graph: every vertex is reachable from some
centre `x i` at distance at most `k - 1 - i`. The centres may repeat or already be burning
when their round starts. For finite graphs, the least such `k` is the usual burning number
[BJR16, Corollary 3]. -/
def IsBurningSequence (G : SimpleGraph V) {k : ℕ} (x : Fin k → V) : Prop :=
  ∀ v, ∃ i, G.Reachable (x i) v ∧ G.dist (x i) v + (i : ℕ) < k

/-- The **burning number** `b(G)`: the least number of rounds needed to burn every vertex
of `G`. -/
noncomputable def burningNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ x : Fin k → V, IsBurningSequence G x}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (0 ≤ ε) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (0 ≤ ε))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (0 ≤ ε)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔ (∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀₁ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀₁ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
      n₀ ≤ Fintype.card V →
        (burningNumber G : ℝ) ≤ (1 + ε) * Real.sqrt (Fintype.card V)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ)  :
    (0 < ε) ↔ (ε ≥ 0) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (¬((0 < ε) ↔ (ε ≥ 0))) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((0 < ε) ↔ (ε ≥ 0)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (ε : ℝ) (hε : 0 < ε) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
