import Mathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Erdős Problem 1013

*References:*
- [erdosproblems.com/1013](https://www.erdosproblems.com/1013)
- [Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.
- [GrYa68] Graver, J. E. and Yackel, J., *Some graph theoretic results associated with Ramsey's
  theorem*. J. Combinatorial Theory 4 (1968), 125-175.
- [DaIl22] Davies, E. and Illingworth, F., *The $\chi$-Ramsey problem for triangle-free graphs*.
  SIAM J. Discrete Math. 36 (2022), 1124-1134.
- [HHKP25] Hefty, Z., Horn, P., King, D. and Pfender, F., *Improving $R(3,k)$ in just two bites*.
  [arXiv:2510.19718](https://arxiv.org/abs/2510.19718) (2025).
-/

section

open Filter Asymptotics

namespace Erdos1013

/-- $h_3(k)$ is the least $n$ such that some triangle-free graph on $n$ vertices has chromatic
number $k$. Triangle-free graphs of every chromatic number exist (Mycielski), so the set is
nonempty and `sInf` is a true minimum. -/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = k}

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k < m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k < m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≥ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (h3 k ≥ m)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≥ h3 k

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (m ≥ h3 k) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) (hG : G.CliqueFree 3), h3 k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) (hG : G.CliqueFree 3), h3 k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) (hG : G.CliqueFree 3), h3 k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) (hG : G.CliqueFree 3), h3 k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) (hG : G.CliqueFree 3), h3 k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG₀ : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), ¬(m < h3 k)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) :
    (h3 k ≤ m) ↔ (¬(m < h3 k)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), ¬(m < h3 k)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), ¬(m < h3 k)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), ¬(m < h3 k)) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) ↔
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), ¬(m < h3 k)) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m > h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m > h3 k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 4) (hk : G.chromaticNumber = k), m ≥ h3 k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hk : G.chromaticNumber = k) :
    (G.CliqueFree 3) ↔ (G.CliqueFree 4) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), h3 k ≤ m) →
    (∀ {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k), m ≤ h3 k) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(0 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(0 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(1 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(0 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(1 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(2 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(0 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(1 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(2 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(3 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(0 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(1 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(2 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(3 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(5 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(0 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(1 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(2 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(3 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(5 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(10 : ℕ), (0 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(1 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(2 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(3 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(5 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(10 : ℕ), (1 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(2 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(3 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(5 : ℕ), (3 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(10 : ℕ), (2 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(3 : ℕ), (10 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example : ∃ (k : ℕ) (m : ℕ), ¬((h3 k ≤ m) ↔ (m ≤ h3 k)) :=
  ⟨(5 : ℕ), (5 : ℕ), by norm_num⟩

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example {k m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.CliqueFree 3) (hk : G.chromaticNumber = k) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
