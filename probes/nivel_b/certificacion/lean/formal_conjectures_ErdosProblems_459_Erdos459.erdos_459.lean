import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 459

*References:*
- [erdosproblems.com/459](https://www.erdosproblems.com/459)
- [ErGr80] P. Erdős and R. L. Graham, *Old and new problems and results in combinatorial number
  theory*, Monographies de L'Enseignement Mathématique 28 (1980), p.91.
- [OEIS A289280](https://oeis.org/A289280)
-/

section

namespace Erdos459

/--
The function from the problem, in its equivalent form: `f u` is the smallest `v > u` all of whose
prime factors divide `u`. (Equivalently, `f u` is the largest `v` such that no `m ∈ (u, v)` is
composed entirely of primes dividing `u * v`.)
-/
noncomputable def f (u : ℕ) : ℕ := sInf {v | u < v ∧ v.primeFactors ⊆ u.primeFactors}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  simp_all

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (2 < u) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (2 < u))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (2 < u))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (2 < u))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (2 < u))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (2 < u))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (2 < u))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (2 < u)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (2 < u)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (2 < u)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (2 < u)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (2 < u)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (2 < u)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 2 ≤ f u)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 2 ≤ f u)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 2 ≤ f u)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 2 ≤ f u)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 2 ≤ f u)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 2 ≤ f u)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 3 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  simp_all

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (3 ≤ u) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (3 ≤ u))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (3 ≤ u)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : u ≥ 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (u ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : u ≥ 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : u ≥ 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : u ≥ 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : u ≥ 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2 ∧ u + 2 ≤ f u

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2 ∧ u + 2 ≤ f u) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu₀ : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu₀ : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu₀ : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu₀ : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu₀ : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : ¬(u < 2)), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (¬(u < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : ¬(u < 2)), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : ¬(u < 2)), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : ¬(u < 2)), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : ¬(u < 2)), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 1 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {u : ℕ} :
    (2 ≤ u) ↔ (1 < u) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 1 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 1 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 1 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔
    (∀ {u : ℕ} (hu : 1 < u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u > 2), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u > 2))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u > 2))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u > 2))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u > 2))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u > 2))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u > 2))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : u ≥ 3), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (u ≥ 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (u ≥ 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (u ≥ 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  simp_all

set_option maxHeartbeats 200000 in
example {u : ℕ}  :
    (2 ≤ u) ↔ (1 ≤ u) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (1 ≤ u))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (1 ≤ u))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (1 ≤ u))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (1 ≤ u))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (1 ≤ u))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (¬((2 ≤ u) ↔ (1 ≤ u))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (1 ≤ u)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (1 ≤ u)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (1 ≤ u)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (1 ≤ u)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (1 ≤ u)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((2 ≤ u) ↔ (1 ≤ u)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 1 < u), u + 3 ≤ f u ∧ f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), (2 ≤ u) ∧ (¬(u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (u + 3 ≤ f u ∧ f u ≤ u ^ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {u : ℕ} (hu : 2 ≤ u), u + 2 ≤ f u ∧ f u ≤ u ^ 2) →
    (∀ {u : ℕ} (hu : 2 ≤ u), f u ≤ u ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (u : ℕ), ¬((u + 2 ≤ f u ∧ f u ≤ u ^ 2) ↔ (f u ≤ u ^ 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {u : ℕ} (hu : 2 ≤ u) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {u : ℕ} (hu : 2 ≤ u) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {u : ℕ} (hu : 2 ≤ u) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {u : ℕ} (hu : 2 ≤ u) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {u : ℕ} (hu : 2 ≤ u) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
