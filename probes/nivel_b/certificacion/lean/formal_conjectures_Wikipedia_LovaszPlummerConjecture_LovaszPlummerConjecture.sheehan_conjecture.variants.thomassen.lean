import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# The Lovász–Plummer conjecture (proved 2011) and Sheehan's conjecture

*References:*
* [Wikipedia](https://en.wikipedia.org/wiki/Petersen%27s_theorem#Related_conjectures)
* [LP86] Lovász, L. and Plummer, M. D. (1986). *Matching Theory.* North-Holland.
* [EKKKN11] Esperet, L., Kardoš, F., King, A. D., Král', D. and Norine, S. (2011).
  "Exponentially many perfect matchings in cubic graphs." *Adv. Math.* 227, pp. 1646--1664.
  [arXiv:1012.2878](https://arxiv.org/abs/1012.2878)
* [Sh77] Sheehan, J. (1977). "The multiplicity of Hamiltonian circuits in a graph." In *Recent
  Advances in Graph Theory*, Academia, Prague, pp. 477--480.
* [Th98] Thomassen, C. (1998). "Independent dominating sets and a second Hamiltonian cycle in
  regular graphs." *J. Combin. Theory Ser. B* 72, pp. 104--109.
-/

section

open SimpleGraph

namespace LovaszPlummerConjecture

variable {V : Type*}

/-- The number of perfect matchings of `G`. -/
noncomputable def perfectMatchingCount (G : SimpleGraph V) : ℕ :=
  {M : G.Subgraph | M.IsPerfectMatching}.ncard

/-- A **Hamiltonian cycle** of `G`: a cycle passing through every vertex. -/
def IsHamiltonianCycle (G : SimpleGraph V) {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ w, w ∈ c.support

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(300 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(299 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(301 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (300 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(300 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(299 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(301 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (300 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 301 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (301 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(300 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(299 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(301 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(302 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (301 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (r ≥ 300) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (hr : 300 ≤ r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (hr : 300 ≤ r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (hr : 300 ≤ r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (hr : 300 ≤ r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hreg : ∀ v, G.degree v = r) (hr : 300 ≤ r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr₀ : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr₀ : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr₀ : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr₀ : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr₀ : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : ¬(r < 300)) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (¬(r < 300)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : ¬(r < 300)) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : ¬(r < 300)) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : ¬(r < 300)) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : ¬(r < 300)) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) :
    (300 ≤ r) ↔ (299 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) ↔
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 < r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r > 300) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r > 300) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(300 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(299 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(301 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r > 300)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : r ≥ 301) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (r ≥ 301) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(300 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(299 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(301 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(302 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (r ≥ 301)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 299 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) →
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (v : V) (c : G.Walk v v) (hc : IsHamiltonianCycle G c), ∃ (w : V) (c' : G.Walk w w), IsHamiltonianCycle G c' ∧
      c'.edges.toFinset ≠ c.edges.toFinset) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    (300 ≤ r) ↔ (299 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(300 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(299 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(301 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(298 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((300 ≤ r) ↔ (299 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (v : V) (c : G.Walk v v) (hr : 300 ≤ r) (hreg : ∀ v, G.degree v = r) (hc : IsHamiltonianCycle G c) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
