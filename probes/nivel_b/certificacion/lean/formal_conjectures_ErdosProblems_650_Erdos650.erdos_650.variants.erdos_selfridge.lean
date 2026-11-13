import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 650

*References:*
- [erdosproblems.com/650](https://www.erdosproblems.com/650)
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [Er86c] Erdős, P., *Some problems on number theory*. (1986), 53-67.
- [Er95c] Erdős, Paul, *Some problems in number theory*. Octogon Math. Mag. (1995), 3-5.
- [ErSu59] Erdős, Pál and Surányi, János, *Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs*. Mat. Lapok (1959), 39-48.
- [VLT26] W. Van Doorn, Y. Li, and Q. Tang, *Optimal bounds for an Erdős problem on matching
  integers to distinct multiples*. arXiv:2603.28636 (2026).
-/

section

namespace Erdos650

/--
`f m` is the largest `r` such that whenever `A ⊆ {1, …, N}` has `m` elements, every interval
in `[1, ∞)` of length `2 * N` contains `r` distinct integers `b 0, …, b (r - 1)`, each `b i`
being divisible by some `a i ∈ A`, where `a 0, …, a (r - 1)` are distinct. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {r : ℕ | ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, A.card = m → ∀ x : ℝ, 1 ≤ x →
    ∃ a b : Fin r → ℕ, (Function.Injective a) ∧ (Function.Injective b) ∧
      (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧ (∀ i, a i ∣ b i)}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) < 2 * m

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) < 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) < 2 * m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) < 2 * m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) < 2 * m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) < 2 * m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) < 2 * m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) < 2 * m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) < 2 * m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) < 2 * m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) < 2 * m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) < 2 * m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) < 2 * m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) < 2 * m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 3 * m

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 3 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≤ 3 * m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≤ 3 * m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≥ 2 * m

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), f (m ^ 2) ≥ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≥ 2 * m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≥ 2 * m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≥ 2 * m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≥ 2 * m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≥ 2 * m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(f (m ^ 2) ≥ 2 * m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≥ 2 * m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≥ 2 * m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≥ 2 * m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≥ 2 * m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≥ 2 * m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (f (m ^ 2) ≥ 2 * m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), 2 * m ≥ f (m ^ 2)

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≥ f (m ^ 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), 2 * m ≥ f (m ^ 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), 2 * m ≥ f (m ^ 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), 2 * m ≥ f (m ^ 2)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), 2 * m ≥ f (m ^ 2)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), ¬(2 * m < f (m ^ 2))

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (m : ℕ) :
    (f (m ^ 2) ≤ 2 * m) ↔ (¬(2 * m < f (m ^ 2))) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), ¬(2 * m < f (m ^ 2))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), ¬(2 * m < f (m ^ 2))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), ¬(2 * m < f (m ^ 2))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) ↔
    (∀ (m : ℕ), ¬(2 * m < f (m ^ 2))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), 2 * m > f (m ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m > f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m > f (m ^ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m > f (m ^ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m > f (m ^ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m > f (m ^ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m > f (m ^ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m > f (m ^ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m > f (m ^ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m > f (m ^ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m > f (m ^ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m > f (m ^ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m > f (m ^ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m > f (m ^ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), 3 * m ≥ f (m ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 3 * m ≥ f (m ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(3 * m ≥ f (m ^ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (3 * m ≥ f (m ^ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), f (m ^ 2) ≤ 2 * m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (m : ℕ), 2 * m ≤ f (m ^ 2)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) →
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (m : ℕ), f (m ^ 2) ≤ 2 * m) →
    (∀ (m : ℕ), 2 * m ≤ f (m ^ 2)) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m ≤ f (m ^ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m ≤ f (m ^ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m ≤ f (m ^ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m ≤ f (m ^ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m ≤ f (m ^ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), (¬(2 * m ≤ f (m ^ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≤ f (m ^ 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≤ f (m ^ 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≤ f (m ^ 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≤ f (m ^ 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≤ f (m ^ 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((f (m ^ 2) ≤ 2 * m) ↔ (2 * m ≤ f (m ^ 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

#eval "FIN_CERTIFICAR"
