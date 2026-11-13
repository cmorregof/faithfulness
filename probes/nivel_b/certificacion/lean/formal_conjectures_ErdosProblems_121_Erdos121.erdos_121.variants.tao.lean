import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 121

*References:*
- [erdosproblems.com/121](https://www.erdosproblems.com/121)
- [Er94b] Erdős, Paul, *Some problems in number theory, combinatorics and combinatorial geometry*.
  Math. Pannon. (1994), 261-269.
- [Er97] Erdős, Paul, *Problems in number theory*. New Zealand J. Math. (1997), 155-160.
- [Er97e] Erdős, Paul, *Some of my favourite unsolved problems*. Math. Japon. (1997), 527-537.
- [Er98] Erdős, Paul, *Some of my new and almost new problems and results in combinatorial number
  theory*. Number theory (Eger, 1996) (1998), 169-180.
- [ESS95] Erdős, P. and Sárközy, A. and Sós, V. T., *On product representations of powers. I*.
  European J. Combin. (1995), 567-588.
- [Er38] P. Erdős, *On sequences of integers no one of which divides the product of two others
  and on related problems*. Tomsk. Gos. Univ. Ucen Zap. (1938), 74-82.
- [Ta24] Tao, T., *On product representations of squares*. arXiv:2405.11610 (2024).
-/

section

open Filter Asymptotics

namespace Erdos121

/-- $F_k(N)$ is the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of no
$k$ many distinct elements of $A$ is a square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = k → ¬ IsSquare (∏ n ∈ S, n)) ∧ A.card = m}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (4 < k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (4 < k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (4 < k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 5 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (5 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (5 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (5 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (k ≥ 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : k ≥ 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔ (∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c₁) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk₀ : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk₀ : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : ¬(k < 4)), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (¬(k < 4)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : ¬(k < 4)), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (k : ℕ) :
    (4 ≤ k) ↔ (3 < k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) ↔
    (∀ (k : ℕ) (hk : 3 < k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k > 4), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k > 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k > 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k > 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : k ≥ 5), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (k ≥ 5) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (k ≥ 5))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(6 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (k ≥ 5)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (k : ℕ) (hk : 3 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) →
    (∀ (k : ℕ) (hk : 4 ≤ k), ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c) * N) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ)  :
    (4 ≤ k) ↔ (3 ≤ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), (¬((4 ≤ k) ↔ (3 ≤ k))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ), ¬((4 ≤ k) ↔ (3 ≤ k)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (k : ℕ) (hk : 4 ≤ k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
