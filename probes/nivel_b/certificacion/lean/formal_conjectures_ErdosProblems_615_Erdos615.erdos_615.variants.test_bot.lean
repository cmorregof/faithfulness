import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 615

A Ramsey–Turán problem of Erdős, Hajnal, Simonovits, Sós, and Szemerédi [EHSSS93]: does there
exist a constant $c > 0$ such that every graph on $n$ vertices with at least $(1/8 - c)n^2$
edges contains either a $K_4$ or an independent set on at least $n/\log n$ vertices? In the
notation of Ramsey–Turán theory this asks whether
$$\mathrm{rt}(n; 4, n/\log n) < (1/8 - c)n^2.$$

This was disproved by Fox, Loh, and Zhao [FLZ15], who showed that
$\mathrm{rt}(n; 4, ne^{-f(n)}) \geq (1/8 - o(1))n^2$ whenever
$f(n) = o(\sqrt{\log n/\log\log n})$. In the other direction Sudakov [Su03] had shown that
$\mathrm{rt}(n; 4, ne^{-f(n)}) = o(n^2)$ whenever $f(n)/\sqrt{\log n} \to \infty$.

*References:*
* [erdosproblems.com/615](https://www.erdosproblems.com/615)
* [EHSSS93] Erdős, P., Hajnal, A., Simonovits, M., Sós, V. T., and Szemerédi, E.,
  *Turán-Ramsey theorems and simple asymptotically extremal structures*. Combinatorica 13
  (1993), 31--56.
* [Su03] Sudakov, B., *A few remarks on Ramsey-Turán-type problems*. J. Combin. Theory Ser. B
  88 (2003), 99--106.
* [FLZ15] Fox, J., Loh, P.-S., and Zhao, Y., *The critical window for the classical
  Ramsey-Turán problem*. Combinatorica 35 (2015), 435--476.
-/

section

open Filter SimpleGraph

namespace Erdos615

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (n ≥ 3) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    ((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn₀ : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn₀ : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : ¬(n < 3)), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (¬(n < 3)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : ¬(n < 3)), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) :
    (3 ≤ n) ↔ (2 < n) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n > 3), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n > 3) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n > 3))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n > 3)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 4), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (n ≥ 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (n ≥ 4))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (n ≥ 4)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : n ≥ 3), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum > (n : ℝ) / Real.log n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 < n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (3 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (3 < n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (3 < n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 4 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≥ (n : ℝ) / Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (4 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (4 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (4 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((⊥ : SimpleGraph (Fin n)).indepNum ≤ (n : ℝ) / Real.log n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n < (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ)  :
    (3 ≤ n) ↔ (2 ≤ n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (¬((3 ≤ n) ↔ (2 ≤ n))) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬((3 ≤ n) ↔ (2 ≤ n)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (hn : 3 ≤ n), (n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) →
    (∀ (n : ℕ) (hn : 2 < n), (n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(4 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), (3 ≤ n) ∧ (¬((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ), ¬(((n : ℝ) / Real.log n ≤ (⊥ : SimpleGraph (Fin n)).indepNum) ↔ ((n : ℝ) / Real.log n ≥ (⊥ : SimpleGraph (Fin n)).indepNum)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (hn : 3 ≤ n) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
