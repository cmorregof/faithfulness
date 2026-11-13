import Mathlib
import FormalConjecturesForMathlib
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option autoImplicit false

-- REQUIERE FormalConjecturesForMathlib (no está en Mathlib v4.34.1):
--   import FormalConjecturesForMathlib.Combinatorics.SetTheory.PartitionRelation
/-!
# Erdős Problem 1167

*References:*
- [erdosproblems.com/1167](https://www.erdosproblems.com/1167)
- [EHMR84] P. Erdős, A. Hajnal, A. Máté and R. Rado, *Combinatorial set theory: partition
  relations for cardinals*. Studies in Logic and the Foundations of Mathematics 106,
  North-Holland (1984).

The original Erdős–Hajnal problem list gives the additional conditions $\gamma \geq 2$, $r < \omega$,
and $\kappa_\alpha > r$. Without $\gamma \geq 2$, the statement is false: taking $\gamma = 1$ and
$\kappa_0 = \aleph_1$ with $\lambda = \aleph_0$ gives a counterexample, since the partition relation
with one color degenerates to a cardinality comparison (see `erdos_1167.unrestricted_is_false`).
Without $\kappa_\alpha > r$ it is also false: with $r = 2$, $\lambda = \aleph_0$ and targets
$(2, \aleph_1)$, the premise $2^{\aleph_0} \to (3, \aleph_1)^3$ holds, but a constant colouring
of the pairs of $\aleph_0$ has neither a red pair nor a blue set of size $\aleph_1$.
-/

section

open Cardinal Ordinal Combinatorics

namespace Erdos1167

universe u

namespace erdos_1167.variants

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (True) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (True) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (True) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
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
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (2 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (2 < r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (2 < r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
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
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : r ≥ 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (r ≥ 2) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : r ≥ 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : r ≥ 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : r ≥ 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : r ≥ 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr₀ : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr₀ : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr₀ : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr₀ : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr₀ : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : ¬(r < 2)) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (¬(r < 2)) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : ¬(r < 2)) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : ¬(r < 2)) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : ¬(r < 2)) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : ¬(r < 2)) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 1 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact and_comm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact not_lt.symm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  exact not_le.symm

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) :
    (2 ≤ r) ↔ (1 < r) := by
  constructor <;> intro _ <;> linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : 1 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  exact Iff.rfl

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : 1 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [gt_iff_lt, ge_iff_le, ne_eq, not_lt, not_le, Set.mem_Icc, Finset.mem_Icc]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : 1 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  simp only [and_comm]

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) ↔
    (∀ (r : ℕ) (hr : 1 < r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  constructor <;> intro h <;> intros <;> apply h <;> assumption

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : r > 2) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (r > 2) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (r > 2) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (r > 2) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
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
  ∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example : Prop :=
  ∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply le_of_lt; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | (apply le_of_lt; assumption)

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply And.left; apply h <;> assumption

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | omega

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; apply h <;> first | assumption | linarith

set_option maxHeartbeats 200000 in
example :
    (∀ (r : ℕ) (hr : 1 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) →
    (∀ (r : ℕ) (hr : 2 ≤ r) (lam : Cardinal.{u}) (hlam : ℵ₀ ≤ lam) (γ : Ordinal.{u}) (hγ : 2 ≤ γ) (n : γ.ToType → ℕ), cardinalPartitionRel ((2 : Cardinal.{u}) ^ lam) (r + 1) γ
        (fun α => (n α : Cardinal.{u}) + 1) →
    cardinalPartitionRel lam r γ (fun α => (n α : Cardinal.{u}))) := by
  intro h; intros; aesop

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | omega)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | linarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | nlinarith)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  constructor <;> intro _ <;> (first | trivial | positivity)

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    (2 ≤ r) ↔ (1 ≤ r) := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
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
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hr : 2 ≤ r) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    False := by
  linarith

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hr : 2 ≤ r) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    False := by
  omega

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hr : 2 ≤ r) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    False := by
  norm_num at *

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hr : 2 ≤ r) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    False := by
  simp_all

set_option maxHeartbeats 200000 in
example (r : ℕ) (lam : Cardinal.{u}) (γ : Ordinal.{u}) (n : γ.ToType → ℕ) (hr : 2 ≤ r) (hlam : ℵ₀ ≤ lam) (hγ : 2 ≤ γ) :
    False := by
  nlinarith

#eval "FIN_CERTIFICAR"
