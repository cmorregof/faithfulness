import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The linear arboricity conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Linear_arboricity)
* [AEH81] Akiyama, J., Exoo, G., and Harary, F. (1981). "Covering and packing in graphs. IV.
  Linear arboricity." *Networks* 11, pp. 69--72.
* [EP84] Enomoto, H. and Péroche, B. (1984). "The linear arboricity of some regular graphs."
  *J. Graph Theory* 8, pp. 309--324.
* [Al88] Alon, N. (1988). "The linear arboricity of graphs." *Israel J. Math.* 62,
  pp. 311--325.
-/

section

namespace LinearArboricityConjecture

variable {V : Type*}

/-- A **linear forest** is a graph whose connected components are paths: an acyclic graph in
which every vertex has at most two neighbours. -/
def IsLinearForest (F : SimpleGraph V) : Prop :=
  F.IsAcyclic ∧ ∀ v, (F.neighborSet v).ncard ≤ 2

/-- `G` decomposes into `k` linear forests: there are `k` linear-forest subgraphs of `G`
such that every edge of `G` lies in exactly one of them. -/
def HasLinearForestDecomposition (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : Fin k → SimpleGraph V, (∀ i, IsLinearForest (D i) ∧ D i ≤ G) ∧
    ∀ u v, G.Adj u v ↔ ∃! i, (D i).Adj u v

/-- The **linear arboricity** `la(G)`: the least number of linear forests into which the edges
of `G` can be partitioned. -/
noncomputable def linearArboricity (G : SimpleGraph V) : ℕ :=
  sInf {k | HasLinearForestDecomposition G k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 ≤ ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
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
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

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
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (ε : ℝ) :
    (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀₁ : ℕ, ∀ Δ : ℕ, Δ₀₁ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε₀ : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

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
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔
    (∀ (ε : ℝ) (hε : ¬(ε ≤ 0)), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε ≥ 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
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
example : Prop :=
  ∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (ε : ℝ) (hε : 0 < ε), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) →
    (∀ (ε : ℝ) (hε : ε > 0), ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), (0 < ε) ∧ (¬(∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (ε : ℝ), ¬((∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 2 + ε) * Δ) ↔ (∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ∀ [DecidableRel G.Adj], G.maxDegree ≤ Δ →
        (linearArboricity G : ℝ) ≤ (1 / 3 + ε) * Δ)) :=
  ⟨(1/2 : ℝ), by norm_num⟩

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
