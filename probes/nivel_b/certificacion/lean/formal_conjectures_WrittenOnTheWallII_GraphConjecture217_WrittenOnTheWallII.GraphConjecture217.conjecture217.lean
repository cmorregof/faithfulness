import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

/-!
# Written on the Wall II - Conjecture 217

Per the WOWII definitions popup linked from this conjecture:

- $L(G)$ is the **maximum number of leaves of a spanning tree** of $G$
  — i.e. `Ls G` in our invariant library.
- $\chi_{\mathrm{residue}=2}(G)$ is the **characteristic function** for the
  predicate $\mathrm{residue}\, G = 2$, i.e. $1$ when $\mathrm{residue}\, G = 2$
  and $0$ otherwise. It is not a connected-component count of any 2-core.

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

section

namespace WrittenOnTheWallII.GraphConjecture217

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The **characteristic function** for the predicate $\mathrm{residue}\, G = 2$:
returns $1$ when $G.\mathrm{residue} = 2$ and $0$ otherwise. This is the WOWII
$\chi_{\mathrm{residue}=2}(G)$ indicator appearing in Conjecture 217. -/
noncomputable def residueEqTwoIndicator (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  if residue G = 2 then 1 else 0

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G < 4 * (residueEqTwoIndicator G : ℝ) + 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (Ls G ≤ 5 * (residueEqTwoIndicator G : ℝ) + 2) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] :
    (∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔ (∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a₁ b : α, ∃ p : G.Walk a₁ b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) ↔
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h₀ : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (4 * (residueEqTwoIndicator G : ℝ) + 2 > Ls G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : 5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (5 * (residueEqTwoIndicator G : ℝ) + 2 ≥ Ls G) := by
  plausible

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) →
    (∀ (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2), ∃ a b : α, ∃ p : G.Walk a b, p.IsHamiltonian) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    (Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) ↔ (True) := by
  plausible

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) (hL : Ls G ≤ 4 * (residueEqTwoIndicator G : ℝ) + 2) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
