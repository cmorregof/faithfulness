import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Coloring.List
/-!
# Erdős Problem 629

*References:*
- [erdosproblems.com/629](https://www.erdosproblems.com/629)
- [ERT80] Erdős, Paul and Rubin, Arthur L. and Taylor, Herbert, *Choosability in graphs*.
  Proceedings of the West Coast Conference on Combinatorics, Graph Theory and Computing (1979),
  Congress. Numer. XXVI (1980), 125-157. [PDF](https://www.renyi.hu/~p_erdos/1980-07.pdf)
- [HMT96] Hanson, Denis and MacGillivray, Gary and Toft, Bjarne, *Choosability of bipartite
  graphs*. Ars Combin. (1996), 183-192.
- [RaSr00] Radhakrishnan, Jaikumar and Srinivasan, Aravind, *Improved bounds and algorithms for
  hypergraph $2$-coloring*. Random Structures Algorithms (2000), 4-32.
-/

section

open Filter SimpleGraph

namespace Erdos629

/-- $n(k)$: the least number of vertices of a bipartite graph $G$ with $\chi_L(G) > k$.
Bipartite means `Colorable 2`, as in [ERT80], which asks for the least number of nodes of a
$2$-colorable graph that is not $k$-choosable. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin m), G.Colorable 2 ∧ k < G.listChromaticNumber}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≤ m

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber > k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≥ n k

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (m ≥ n k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≥ n k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≥ n k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≥ n k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≥ n k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : k < G.listChromaticNumber) (hG : G.Colorable 2), n k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : k < G.listChromaticNumber) (hG : G.Colorable 2), n k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : k < G.listChromaticNumber) (hG : G.Colorable 2), n k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : k < G.listChromaticNumber) (hG : G.Colorable 2), n k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : k < G.listChromaticNumber) (hG : G.Colorable 2), n k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), ¬(m < n k)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (n k ≤ m) ↔ (¬(m < n k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), ¬(m < n k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), ¬(m < n k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), ¬(m < n k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), ¬(m < n k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber ≥ k), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (G.listChromaticNumber ≥ k) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : G.listChromaticNumber > k), n k ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (n k ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m > n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m > n k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k ≤ G.listChromaticNumber), m ≥ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (k ≤ G.listChromaticNumber) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), m ≤ n k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((n k ≤ m) ↔ (m ≤ n k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2), n k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber), n k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) :
    (k < G.listChromaticNumber) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.Colorable 2) (hk : k < G.listChromaticNumber) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
