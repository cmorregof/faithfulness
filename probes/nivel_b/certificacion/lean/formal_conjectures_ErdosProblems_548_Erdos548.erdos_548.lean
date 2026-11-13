import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 548

*References:*
- [erdosproblems.com/548](https://www.erdosproblems.com/548)
- [BrDo96] Brandt, Stephan and Dobson, Edward, *The Erdős-Sós conjecture for graphs of girth {$5$}*.
  Discrete Math. (1996), 411-414.
- [Er78] Erdős, Paul, *Problems and results in combinatorial analysis and combinatorial number
  theory*. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978) (1978), 29-40.
- [ErGa59] Erdős, P. and Gallai, T., *On maximal paths and circuits of graphs*. Acta Math. Acad.
  Sci. Hungar. (1959), 337-356 (unbound insert).
- [SaWo97] Saclé, Jean-François and Woźniak, Mariusz, *The Erdős-Sós conjecture for graphs without
  {$C_4$}*. J. Combin. Theory Ser. B (1997), 367-372.
- [WLL00] Wang, Min and Li, Guo-jun and Liu, Ai-de, *A result of Erdős-Sós conjecture*. Ars Combin.
  (2000), 123-127.
- [YiLi04] Yin, Jian-hua and Li, Jiong-sheng, *The Erdős-Sós conjecture for graphs whose complements
  contain no {$C_4$}*. Acta Math. Appl. Sin. Engl. Ser. (2004), 397-400.
-/

section

open SimpleGraph

namespace Erdos548

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (True)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 < n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (k + 1 < n) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (k + 1 < n)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (n ≥ k + 1) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk₀ : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk₀ : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk₀ : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk₀ : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk₀ : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : ¬(n < k + 1)) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) :
    (k + 1 ≤ n) ↔ (¬(n < k + 1)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : ¬(n < k + 1)) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : ¬(n < k + 1)) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : ¬(n < k + 1)) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) ↔
    (∀ (n k : ℕ) (hk : ¬(n < k + 1)) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n > k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    (k + 1 ≤ n) ↔ (n > k + 1) := by
  plausible

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (n : ℕ) (k : ℕ), ¬((k + 1 ≤ n) ↔ (n > k + 1)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (n k : ℕ) (hk : k + 1 ≤ n) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) →
    (∀ (n k : ℕ) (hk : n ≥ k + 1) (G : SimpleGraph (Fin n)) (H : ((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree), T.IsContained G) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (hT : T.IsTree) :
    (((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) ↔ (((k : ℚ) - 1) / 3 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) := by
  plausible

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (n k : ℕ) (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin (k + 1))) (hk : k + 1 ≤ n) (H : ((k : ℚ) - 1) / 2 * n + 1 ≤ (G.edgeSet.ncard : ℚ)) (hT : T.IsTree) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
