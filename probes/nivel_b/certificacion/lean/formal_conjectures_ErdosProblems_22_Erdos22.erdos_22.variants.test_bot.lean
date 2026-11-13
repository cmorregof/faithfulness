import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 22

The central problem of Ramsey–Turán theory: writing $\mathrm{rt}(n; k, \ell)$ for the maximum
number of edges of a $K_k$-free graph on $n$ vertices whose largest independent set has size
less than $\ell$, is it true that for every $\epsilon > 0$ and all sufficiently large $n$
$$\mathrm{rt}(n; 4, \epsilon n) \geq n^2/8?$$

Conjectured by Bollobás and Erdős [BoEr76], who constructed such a graph with
$(1/8 + o(1))n^2$ edges. Together with the matching upper bound
$\mathrm{rt}(n; 4, \epsilon n) \leq (1/8 + o(1))n^2$ of Szemerédi [Sz72], this determines the
Ramsey–Turán density of $K_4$ to be $1/8$. The conjecture as stated was proved by Fox, Loh,
and Zhao [FLZ15].

*References:*
* [erdosproblems.com/22](https://www.erdosproblems.com/22)
* [BoEr76] Bollobás, B. and Erdős, P., *On a Ramsey-Turán type problem*. J. Combin. Theory
  Ser. B 21 (1976), 166--168.
* [Sz72] Szemerédi, E., *On graphs containing no complete subgraph with 4 vertices*
  (Hungarian). Mat. Lapok 23 (1972), 113--116.
* [FLZ15] Fox, J., Loh, P.-S., and Zhao, Y., *The critical window for the classical
  Ramsey-Turán problem*. Combinatorica 35 (2015), 435--476.
-/

section

open Filter SimpleGraph

namespace Erdos22

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(6 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(6 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(6 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (ε > 0) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2 ∧ (⊥ : SimpleGraph (Fin n)).CliqueFree 4) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε₀ : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε₀ : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε₀ : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε₀ : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε₀ : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : ¬(ε ≤ 0)), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) :
    (0 < ε) ↔ (¬(ε ≤ 0)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ¬(ε ≤ 0)), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ¬(ε ≤ 0)), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ¬(ε ≤ 0)), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔
    (∀ (n : ℕ) (ε : ℝ) (hε : ¬(ε ≤ 0)), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) < (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(6 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(6 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(6 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (6 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 5 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : ε > 0), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (-1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), (0 < ε) ∧ (¬((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≥ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) →
    (∀ (n : ℕ) (ε : ℝ) (hε : 0 < ε), (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (1 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(0 : ℕ), (5 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(2 : ℕ), (3 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(8 : ℕ), (4 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(4 : ℕ), (7 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(3 : ℕ), (8 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(5 : ℕ), (2 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (ε : ℝ), ¬(((⊥ : SimpleGraph (Fin n)).CliqueFree 4 ∧
      (((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2) ↔ ((((⊥ : SimpleGraph (Fin n)).edgeFinset.card : ℝ)) ≤ (1 / 8 + ε) * n ^ 2)) :=
  ⟨(1 : ℕ), (0 : ℝ), by norm_num⟩

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
