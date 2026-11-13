import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 387

*References:*
 - [erdosproblems.com/387](https://www.erdosproblems.com/387)
 - [ErGr76b] Erdős, P. and Graham, R. L., *On the prime factors of
   ${n \choose k}$*. Fibonacci Quart. (1976), 348-352.
 - [Er78g] Erdős, Pál, *On prime factors of binomial coefficients. II*. Mat. Lapok
   (1978/82), 307-316.
 - [ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial
   number theory*. Monographies de L'Enseignement Mathematique (1980).
 - [Sc58] Schinzel, A., *Sur un problème de P. Erdős*. Colloq. Math. (1958), 198-204.
 - [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
 - [Fa66] Faulkner, M. "On a theorem of Sylvester and Schur." Journal of the London Mathematical
    Society 1.1 (1966): 107-110.
 - [BNPZ26] Bui, H., Naprienko, S., Pratt, K., and Zaharescu, A. Binomial coefficients with
    divisors avoiding an interval. arXiv:2605.21221 (2026).
-/

section

open Filter

namespace Erdos387

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (1 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (k ≤ n) ∧ (¬((1 ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((1 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : n ≥ 1) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (n ≥ 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : n ≥ 1) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : n ≥ 1) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : n ≥ 1) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : n ≥ 1) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔ (∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d₁ : ℕ,
    (d₁ : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d₁ ∣ n.choose k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hk : k ≤ n) (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn₀ : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn₀ : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn₀ : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn₀ : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn₀ : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : ¬(n < 1)) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (¬(n < 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : ¬(n < 1)) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : ¬(n < 1)) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : ¬(n < 1)) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : ¬(n < 1)) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 0 < n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} :
    (1 ≤ n) ↔ (0 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 0 < n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 0 < n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 0 < n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) ↔
    (∀ {n : ℕ} {k : ℕ} (hn : 0 < n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) →
    (∀ {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n), ∃ d : ℕ,
    (d : ℝ) ∈ Set.Icc (n / k : ℝ) n ∧ d ∣ n.choose k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) :
    (k ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), (1 ≤ n) ∧ (¬((k ≤ n) ↔ (True))) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {n : ℕ} {k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
