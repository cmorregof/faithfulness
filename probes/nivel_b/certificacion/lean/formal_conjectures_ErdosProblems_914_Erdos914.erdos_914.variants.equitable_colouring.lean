import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 914

*References:*
- [erdosproblems.com/914](https://www.erdosproblems.com/914)
- [CoHa63] Corrádi, K. and Hajnal, A., *On the maximal number of independent circuits in a graph*.
  Acta Math. Acad. Sci. Hungar. (1963), 423-439.
- [HaSz70] Hajnal, A. and Szemerédi, E., *Proof of a conjecture of P. Erdős*. (1970), 601-623.
- [KiKo08] Kierstead, H. A. and Kostochka, A. V., *A short proof of the Hajnal-Szemerédi theorem on
  equitable colouring*. Combin. Probab. Comput. (2008), 265-270.
-/

section

namespace Erdos914

universe u_c1 u_c2 u_c3 u_c4 u_c5 u_c6 u_c7 u_c8 u_c9 u_c10 u_c11 u_c12 u_c13 u_c14 u_c15 u_c16 u_c17 u_c18 u_c19 u_c20 u_c21 u_c22 u_c23 u_c24 u_c25 u_c26 u_c27 u_c28 u_c29 u_c30 u_c31 u_c32 u_c33 u_c34 u_c35 u_c36 u_c37
set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hm : 1 ≤ m) {V : Type u_c2} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c1} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c3} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c4} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 < r) (hm : 1 ≤ m) {V : Type u_c5} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c6} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (2 < r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (2 < r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : r ≥ 2) (hm : 1 ≤ m) {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c9} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (r ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : r ≥ 2) (hm : 1 ≤ m) {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : r ≥ 2) (hm : 1 ≤ m) {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : r ≥ 2) (hm : 1 ≤ m) {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c7} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : r ≥ 2) (hm : 1 ≤ m) {V : Type u_c8} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c12} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔ (∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c10} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c11} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C₁ : G.Coloring (Fin m), ∀ i, (C₁.colorClass i).ncard = r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c13} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hm : 1 ≤ m) (hr : 2 ≤ r) {V : Type u_c14} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr₀ : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr₀ : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr₀ : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr₀ : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c16} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr₀ : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c17} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : ¬(r < 2)) (hm : 1 ≤ m) {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c21} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : ¬(r < 2)) (hm : 1 ≤ m) {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : ¬(r < 2)) (hm : 1 ≤ m) {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : ¬(r < 2)) (hm : 1 ≤ m) {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c19} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : ¬(r < 2)) (hm : 1 ≤ m) {V : Type u_c20} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 1 < r) (hm : 1 ≤ m) {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c24} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (2 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 ≤ m) {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 ≤ m) {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 ≤ m) {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c22} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) ↔
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 ≤ m) {V : Type u_c23} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c25} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : r > 2) (hm : 1 ≤ m) {V : Type u_c26} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c27} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (r > 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (r > 2)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) {V : Type u_c29} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c28} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c30} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (r : ℕ), ¬((2 ≤ r) ↔ (1 ≤ r)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c31} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 1 < r) (hm : 1 < m) {V : Type u_c32} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c33} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (1 < m) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (1 < m)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {r m : ℕ} (hr : 2 ≤ r) {V : Type u_c35} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) →
    (∀ {r m : ℕ} (hr : 2 ≤ r) (hm : 1 ≤ m) {V : Type u_c34} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1), ∃ C : G.Coloring (Fin m), ∀ i, (C.colorClass i).ncard = r) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c36} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    (1 ≤ m) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (True)) :=
  ⟨(1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (True)) :=
  ⟨(0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (True)) :=
  ⟨(2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (True)) :=
  ⟨(3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (True)) :=
  ⟨(5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (m : ℕ), ¬((1 ≤ m) ↔ (True)) :=
  ⟨(10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c37} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c37} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c37} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c37} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {r m : ℕ} {V : Type u_c37} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hr : 2 ≤ r) (hm : 1 ≤ m) (hV : Fintype.card V = r * m) (hdeg : G.maxDegree ≤ m - 1) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
