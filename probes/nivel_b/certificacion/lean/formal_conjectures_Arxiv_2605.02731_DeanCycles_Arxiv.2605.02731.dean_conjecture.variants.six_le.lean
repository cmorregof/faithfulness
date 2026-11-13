import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Circumference
/-!
# Dean's conjecture on cycles of length divisible by `k`

*References:*
- [arxiv/2605.02731](https://arxiv.org/abs/2605.02731)
  **Existence of cycles of length divisible by 3 or 4**
  by *Ilkyoo Choi, Hojin Chu, Ringi Kim, Boram Park*, where this is Conjecture 1.1.
- [De88] Dean, N., Open problem, in Cycles and Rays. (1988).
- [DeLeSa93] Dean, N. and Lesniak, L. and Saito, A., Cycles of length 0 modulo 4 in graphs.
  Discrete Math. (1993), 133--139.
- [ChSa94] Chen, G. and Saito, A., Graphs with a cycle of length divisible by three.
  J. Combin. Theory Ser. B (1994), 277--292.
- [LuMaZh26] Luo, Yufan and Ma, Jie and Zhao, Ziyuan, Dean's conjecture and cycles modulo k.
  [arXiv:2601.13552](https://arxiv.org/abs/2601.13552) (2026).
-/

section

open SimpleGraph

namespace Arxiv.«2605.02731»

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (6 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (6 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 7 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (7 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (7 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (k ≥ 6) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m₁ ∈ G.cycleLengths, k ∣ m₁

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ m ∈ G.cycleLengths, k ∣ m) ↔ (∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m₁ ∈ G.cycleLengths, k ∣ m₁) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk₀ : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk₀ : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk₀ : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk₀ : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk₀ : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : ¬(k < 6)) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (¬(k < 6)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : ¬(k < 6)) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : ¬(k < 6)) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : ¬(k < 6)) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : ¬(k < 6)) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (6 ≤ k) ↔ (5 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k > 6) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k > 6) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k > 6)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : k ≥ 7) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (k ≥ 7) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(8 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (k ≥ 7)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree) :
    (6 ≤ k) ↔ (5 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(7 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((6 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 6 ≤ k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k ≤ G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 5 < k) (G : SimpleGraph V) [DecidableRel G.Adj] (hG : k < G.minDegree), ∃ m ∈ G.cycleLengths, k ∣ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) :
    (k ≤ G.minDegree) ↔ (k < G.minDegree) := by
  plausible

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) (hG : k ≤ G.minDegree) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) (hG : k ≤ G.minDegree) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) (hG : k ≤ G.minDegree) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) (hG : k ≤ G.minDegree) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (hk : 6 ≤ k) (hG : k ≤ G.minDegree) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
